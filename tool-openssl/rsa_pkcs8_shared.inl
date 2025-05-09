// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Include only from rsa_pkcs8_shared.h

namespace awslc_test {

// Implementation of the TestKeyToolOptionErrors template function
// Tests for expected error conditions when invalid options are provided to CLI tools
template<typename ToolFunc>
void TestKeyToolOptionErrors(ToolFunc tool_func, const std::vector<std::string>& args) {
    if (args.empty()) {
        ADD_FAILURE() << "Empty argument list provided to TestKeyToolOptionErrors";
        return;
    }
    
    args_list_t c_args;
    for (const auto& arg : args) {
        c_args.push_back(arg.c_str());
    }
    
    bool result = tool_func(c_args);
    ASSERT_FALSE(result) << "Expected error not triggered for args: " 
                        << args[0] << (args.size() > 1 ? "..." : "");
}

} // namespace awslc_test
