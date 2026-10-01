// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/ui.h>

#include <gtest/gtest.h>

#include <openssl/mem.h>

namespace {

UI_METHOD *g_ui_method = nullptr;

int ui_open(UI *ui) { return UI_method_get_opener(UI_OpenSSL())(ui); }
int ui_read(UI *ui, UI_STRING *uis) {
  return UI_method_get_reader(UI_OpenSSL())(ui, uis);
}
int ui_write(UI *ui, UI_STRING *uis) {
  return UI_method_get_writer(UI_OpenSSL())(ui, uis);
}
int ui_close(UI *ui) { return UI_method_get_closer(UI_OpenSSL())(ui); }

void setup_ui_method() {
  g_ui_method = UI_create_method("OpenSSL application user interface");
  UI_method_set_opener(g_ui_method, ui_open);
  UI_method_set_reader(g_ui_method, ui_read);
  UI_method_set_writer(g_ui_method, ui_write);
  UI_method_set_closer(g_ui_method, ui_close);
}

void cleanup_ui_method() {
  if (g_ui_method) {
    UI_destroy_method(g_ui_method);
    g_ui_method = nullptr;
  }
}

TEST(UITest, ApplicationsShim) {
  for (int i = 0; i < 2; i++) {
    setup_ui_method();
    EXPECT_EQ(nullptr, g_ui_method);
    // Although not reached by Mosquitto today, the forwarding callbacks must
    // fail safely rather than dereference a NULL function pointer.
    EXPECT_EQ(0, ui_open(nullptr));
    EXPECT_EQ(0, ui_read(nullptr, nullptr));
    EXPECT_EQ(0, ui_write(nullptr, nullptr));
    EXPECT_EQ(0, ui_close(nullptr));
    cleanup_ui_method();
    cleanup_ui_method();
    EXPECT_EQ(nullptr, g_ui_method);
  }
}

int unexpected_session_callback(UI *ui) {
  ADD_FAILURE() << "UI stub invoked an application callback";
  return 1;
}

int unexpected_string_callback(UI *ui, UI_STRING *uis) {
  ADD_FAILURE() << "UI stub invoked an application callback";
  return 1;
}

TEST(UITest, MethodStubs) {
  EXPECT_EQ(nullptr, UI_create_method(nullptr));
  EXPECT_EQ(nullptr, UI_create_method("test"));
  UI_METHOD *builtin = UI_OpenSSL();
  ASSERT_NE(nullptr, builtin);
  EXPECT_EQ(builtin, UI_OpenSSL());

  UI_METHOD dummy = {0};
  UI ui = {0};
  UI_METHOD *methods[] = {nullptr, builtin, &dummy};
  for (UI_METHOD *method : methods) {
    EXPECT_EQ(-1, UI_method_set_opener(method, nullptr));
    EXPECT_EQ(-1, UI_method_set_writer(method, nullptr));
    EXPECT_EQ(-1, UI_method_set_reader(method, nullptr));
    EXPECT_EQ(-1, UI_method_set_closer(method, nullptr));
    EXPECT_EQ(-1, UI_method_set_opener(method, unexpected_session_callback));
    EXPECT_EQ(-1, UI_method_set_writer(method, unexpected_string_callback));
    EXPECT_EQ(-1, UI_method_set_reader(method, unexpected_string_callback));
    EXPECT_EQ(-1, UI_method_set_closer(method, unexpected_session_callback));

    const UI_METHOD *const_method = method;
    auto opener = UI_method_get_opener(const_method);
    auto writer = UI_method_get_writer(const_method);
    auto reader = UI_method_get_reader(const_method);
    auto closer = UI_method_get_closer(const_method);
    ASSERT_NE(nullptr, opener);
    ASSERT_NE(nullptr, writer);
    ASSERT_NE(nullptr, reader);
    ASSERT_NE(nullptr, closer);
    UI *args[] = {nullptr, &ui};
    for (UI *arg : args) {
      EXPECT_EQ(0, opener(arg));
      EXPECT_EQ(0, writer(arg, nullptr));
      EXPECT_EQ(0, reader(arg, nullptr));
      EXPECT_EQ(0, closer(arg));
    }

    // Destruction is a no-op, even for static and stack-allocated dummies.
    UI_destroy_method(method);
    EXPECT_EQ(0, UI_method_get_opener(method)(nullptr));
  }
}

TEST(UITest, ExistingStubs) {
  EXPECT_EQ(nullptr, UI_new());
  UI_free(nullptr);
  UI *allocated = static_cast<UI *>(OPENSSL_malloc(sizeof(UI)));
  ASSERT_NE(nullptr, allocated);
  UI_free(allocated);

  UI ui = {0};
  UI *args[] = {nullptr, &ui};
  for (UI *arg : args) {
    char buf[] = "unchanged";
    EXPECT_EQ(-1, UI_add_input_string(arg, "prompt", 0, buf, 0, sizeof(buf)));
    EXPECT_EQ(-1, UI_add_verify_string(arg, "prompt", 0, buf, 0, sizeof(buf),
                                       "test"));
    EXPECT_STREQ("unchanged", buf);
    EXPECT_EQ(-1, UI_add_info_string(arg, "info"));
    EXPECT_EQ(-1, UI_process(arg));
  }
}

}  // namespace
