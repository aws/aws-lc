// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// currently only supports shared builds for Linux and MacOS
#include <inttypes.h>
#include <openssl/base.h>
#include <openssl/hmac.h>
#include <tool/internal.h>
#include <LIEF/LIEF.hpp>
#include <cstring>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <vector>


// Define logging macros to maintain similar behavior to the original code
#define LOG_ERROR(fmt, ...) fprintf(stderr, "Error: " fmt "\n", ##__VA_ARGS__)
#define LOG_INFO(fmt, ...) fprintf(stdout, fmt "\n", ##__VA_ARGS__)

static const argument_t kArguments[] = {
    {"-in-object", kRequiredArgument, "Input object file path"},
    {"-o", kRequiredArgument, "Output file path"},
    {"-apple", kBooleanArgument, "Apple platform flag"},
    {"", kOptionalArgument, ""}  // Terminating element
};

static void print_usage() {
  LOG_INFO(
      "Usage: inject_hash_cpp -o output_file -in-object input_file [-apple]");
  PrintUsage(kArguments);
}

// UninitHashValue is the default hash value that we inject into the module.
// This value need only be distinct, i.e. so that we can safely
// search-and-replace it in an object file.
static constexpr uint8_t UNINIT_HASH[32] = {
    0xae, 0x2c, 0xea, 0x2a, 0xbd, 0xa6, 0xf3, 0xec, 0x97, 0x7f, 0x9b,
    0xf6, 0x94, 0x9a, 0xfc, 0x83, 0x68, 0x27, 0xcb, 0xa0, 0xa0, 0x9f,
    0x6b, 0x6f, 0xde, 0x52, 0xcd, 0xe2, 0xcd, 0xff, 0x31, 0x80};


// Convert a uint64_t value into its little-endian byte representation.
// Returns: true if conversion was successful, false if buffer is too small
static bool size_to_little_endian(size_t value_to_convert, uint8_t *result,
                                  size_t result_len) {
  static const size_t UINT64_BYTES = sizeof(uint64_t);
  if (result == nullptr || result_len < UINT64_BYTES) {
    return false;
  }

  for (size_t i = 0; i < UINT64_BYTES; i++) {
    result[i] = (value_to_convert >> (i * 8)) & 0xFF;
  }
  return true;
}

// Extract module content using LIEF for Apple platforms
static bool extract_apple_modules(const std::string &input_path,
                                  std::vector<uint8_t> &text_module,
                                  std::vector<uint8_t> &rodata_module) {
  // Parse the binary with LIEF
  auto binary = LIEF::MachO::Parser::parse(input_path);
  if (!binary || binary->empty()) {
    LOG_ERROR("Failed to parse binary file");
    return false;
  }

  // For Mach-O, work with the first binary in the fat binary
  auto macho = binary->at(0);
  if (!macho) {
    LOG_ERROR("Failed to get Mach-O binary");
    return false;
  }

  // Find boundary symbols
  const auto *text_start = macho->get_symbol("_BORINGSSL_bcm_text_start");
  if (!text_start) {
    LOG_ERROR("Could not find BORINGSSL_bcm_text_start symbol");
    return false;
  }
  const auto *text_end = macho->get_symbol("_BORINGSSL_bcm_text_end");
  if (!text_end) {
    LOG_ERROR("Could not find BORINGSSL_bcm_text_end symbol");
    return false;
  }
  // rodata linker markers have to be present for the shared builds. They are
  // only optional in the case of static builds where rodata linker markers are
  // not present since rodata is embedded inside the text section itself.
  const auto *rodata_start = macho->get_symbol("_BORINGSSL_bcm_rodata_start");
  if (!rodata_start) {
    LOG_ERROR("Could not find BORINGSSL_bcm_rodata_start symbol");
    return false;
  }
  const auto *rodata_end = macho->get_symbol("_BORINGSSL_bcm_rodata_end");
  if (!rodata_end) {
    LOG_ERROR("Could not find BORINGSSL_bcm_rodata_end symbol");
    return false;
  }


  // Find the sections containing these symbols
  const LIEF::MachO::Section *text_section = nullptr;
  const LIEF::MachO::Section *rodata_section = nullptr;

  const auto *text_segment = macho->get_segment("__TEXT");
  if (!text_segment) {
    LOG_ERROR("Could not find __TEXT segment");
    return false;
  }

  for (const auto &section : text_segment->sections()) {
    if (section.name() == "__text") {
      text_section = &section;
      LOG_INFO("Found __text section at virtual address: 0x%" PRIx64,
               section.virtual_address());
    } else if (section.name() == "__const") {
      rodata_section = &section;
      LOG_INFO("Found __const section at virtual address: 0x%" PRIx64,
               section.virtual_address());
    }
  }

  if (!text_section) {
    LOG_ERROR("Could not locate __text section");
    return false;
  }

  if (!rodata_section) {
    LOG_ERROR("Could not locate __const section");
    return false;
  }

  // Calculate module boundaries within sections
  auto text_sec_addr = text_section->virtual_address();
  uint64_t text_start_offset = text_start->value() - text_sec_addr;
  uint64_t text_end_offset = text_end->value() - text_sec_addr;

  if (text_start_offset >= text_end_offset ||
      text_end_offset > text_section->content().size()) {
    LOG_ERROR("Invalid text module boundaries");
    return false;
  }

  // Extract text module
  auto content = text_section->content();
  text_module.resize(text_end_offset - text_start_offset);
  std::memcpy(text_module.data(), content.data() + text_start_offset,
              text_module.size());

  // Extract rodata module if present
  auto rodata_sec_addr = rodata_section->virtual_address();
  uint64_t rodata_start_offset = rodata_start->value() - rodata_sec_addr;
  uint64_t rodata_end_offset = rodata_end->value() - rodata_sec_addr;

  if (rodata_start_offset >= rodata_end_offset ||
      rodata_end_offset > rodata_section->content().size()) {
    LOG_ERROR("Invalid rodata module boundaries");
    return false;
  }

  auto rodata_content = rodata_section->content();
  rodata_module.resize(rodata_end_offset - rodata_start_offset);
  std::memcpy(rodata_module.data(), rodata_content.data() + rodata_start_offset,
              rodata_module.size());

  return true;
}

static bool extract_linux_modules(const std::string &input_path,
                                  std::vector<uint8_t> &text_module,
                                  std::vector<uint8_t> &rodata_module) {
  // Parse the binary with LIEF
  auto binary = LIEF::ELF::Parser::parse(input_path);
  if (!binary) {
    LOG_ERROR("Failed to parse binary file");
    return false;
  }
  auto elf = binary.get();
  if (!elf) {
    LOG_ERROR("Failed to get ELF binary");
    return false;
  }

  // Find boundary symbols
  const auto *text_start = elf->get_symbol("BORINGSSL_bcm_text_start");
  if (!text_start) {
    LOG_ERROR("Could not find BORINGSSL_bcm_text_start symbol");
    return false;
  }
  const auto *text_end = elf->get_symbol("BORINGSSL_bcm_text_end");
  if (!text_end) {
    LOG_ERROR("Could not find BORINGSSL_bcm_text_end symbol");
    return false;
  }

  // rodata linker markers have to be present for the shared builds. They are
  // only optional in the case of static builds where rodata linker markers are
  // not present since rodata is embedded inside the text section itself.
  const auto *rodata_start = elf->get_symbol("BORINGSSL_bcm_rodata_start");
  if (!rodata_start) {
    LOG_ERROR("Could not find BORINGSSL_bcm_rodata_start symbol");
    return false;
  }
  const auto *rodata_end = elf->get_symbol("BORINGSSL_bcm_rodata_end");
  if (!rodata_end) {
    LOG_ERROR("Could not find BORINGSSL_bcm_rodata_end symbol");
    return false;
  }


  // Find the sections containing these symbols
  const LIEF::ELF::Section *text_section = nullptr;
  const LIEF::ELF::Section *rodata_section = nullptr;

  for (const auto &section : elf->sections()) {
    if (section.name() == ".text") {
      text_section = &section;
      LOG_INFO("Found .text section at virtual address: 0x%" PRIx64,
               section.virtual_address());
    }
    if (section.name() == ".rodata") {
      rodata_section = &section;
      LOG_INFO("Found .rodata section at virtual address: 0x%" PRIx64,
               section.virtual_address());
    }
  }

  if (!text_section) {
    LOG_ERROR("Could not locate .text section");
    return false;
  }
  if (!rodata_section) {
    LOG_ERROR("Could not locate .rodata section");
    return false;
  }

  // Calculate module boundaries within sections
  auto text_sec_addr = text_section->virtual_address();
  uint64_t text_start_offset = text_start->value() - text_sec_addr;
  uint64_t text_end_offset = text_end->value() - text_sec_addr;

  if (text_start_offset >= text_end_offset ||
      text_end_offset > text_section->content().size()) {
    LOG_ERROR("Invalid text module boundaries");
    return false;
  }

  // Extract text module
  auto content = text_section->content();
  text_module.resize(text_end_offset - text_start_offset);
  std::memcpy(text_module.data(), content.data() + text_start_offset,
              text_module.size());

  // Extract rodata module if present

  auto rodata_sec_addr = rodata_section->virtual_address();
  uint64_t rodata_start_offset = rodata_start->value() - rodata_sec_addr;
  uint64_t rodata_end_offset = rodata_end->value() - rodata_sec_addr;

  if (rodata_start_offset >= rodata_end_offset ||
      rodata_end_offset > rodata_section->content().size()) {
    LOG_ERROR("Invalid rodata module boundaries");
    return false;
  }

  auto rodata_content = rodata_section->content();
  rodata_module.resize(rodata_end_offset - rodata_start_offset);
  std::memcpy(rodata_module.data(), rodata_content.data() + rodata_start_offset,
              rodata_module.size());


  return true;
}

// Calculate HMAC hash
static bool calculate_hash(const std::vector<uint8_t> &text_module,
                           const std::vector<uint8_t> &rodata_module,
                           std::vector<uint8_t> &out_hash) {
  out_hash.resize(SHA256_DIGEST_LENGTH);
  uint8_t zero_key[64] = {0};
  uint8_t length_bytes[8];

  bssl::ScopedHMAC_CTX ctx;
  if (!ctx.get()) {
    LOG_ERROR("Failed to create HMAC context");
    return false;
  }

  if (!HMAC_Init_ex(ctx.get(), zero_key, sizeof(zero_key), EVP_sha256(),
                    nullptr)) {
    LOG_ERROR("HMAC_Init failed");
    return false;
  }

  // Add text module size and content
  if (!size_to_little_endian(text_module.size(), length_bytes,
                             sizeof(length_bytes))) {
    LOG_ERROR("Buffer too small for little-endian conversion");
    return false;
  }
  if (!HMAC_Update(ctx.get(), length_bytes, sizeof(length_bytes)) ||
      !HMAC_Update(ctx.get(), text_module.data(), text_module.size())) {
    LOG_ERROR("HMAC_Update failed for text module");
    return false;
  }

  // Add rodata module size and content if present
  if (!rodata_module.empty()) {
    if (!size_to_little_endian(rodata_module.size(), length_bytes,
                               sizeof(length_bytes))) {
      LOG_ERROR("Buffer too small for little-endian conversion");
      return false;
    }
    if (!HMAC_Update(ctx.get(), length_bytes, sizeof(length_bytes)) ||
        !HMAC_Update(ctx.get(), rodata_module.data(), rodata_module.size())) {
      LOG_ERROR("HMAC_Update failed for rodata module");
      return false;
    }
  }

  unsigned int hash_len;
  if (!HMAC_Final(ctx.get(), out_hash.data(), &hash_len)) {
    LOG_ERROR("HMAC_Final failed");
    return false;
  }

  // Print calculated hash for reference
  std::string hash_str;
  for (unsigned int i = 0; i < hash_len; i++) {
    char hex[3];
    snprintf(hex, sizeof(hex), "%02X", out_hash[i]);
    hash_str += hex;
  }
  LOG_INFO("Calculated hash: %s", hash_str.c_str());

  return true;
}

static bool process(const std::string &input_path,
                    const std::string &output_path, bool is_apple) {
  std::ifstream input_file(
      input_path, std::ios::binary |
                      std::ios::ate);  // Open the file in binary mode and move
                                       // to the end to get size (the ate
                                       // pointer gets to the end of the file)
  if (!input_file) {
    LOG_ERROR("Failed to open input file: %s", input_path.c_str());
    return false;
  }

  size_t file_size = input_file.tellg();
  input_file.seekg(0, std::ios::beg);  // Move back to the beginning of the file
                                       // to read its content

   // Read the input binary file
  std::vector<uint8_t> binary_data(file_size);
  if (!input_file.read(reinterpret_cast<char *>(binary_data.data()),
                       file_size)) {
    LOG_ERROR("Failed to read file %s", input_path.c_str());
    return false;
  }

  //  Extract module content based on platform
  std::vector<uint8_t> text_module, rodata_module;
  if (is_apple) {
    if (!extract_apple_modules(input_path, text_module, rodata_module)) {
      LOG_ERROR("Failed to extract modules from Apple binary");
      return false;
    }
  } else {
    if (!extract_linux_modules(input_path, text_module, rodata_module)) {
      LOG_ERROR("Failed to extract modules from Linux binary");
      return false;
    }
  }

  //  Find the placeholder hash in the binary
  size_t hash_pos = std::string::npos;
  for (size_t i = 0; i <= binary_data.size() - sizeof(UNINIT_HASH); i++) {
    if (std::memcmp(binary_data.data() + i, UNINIT_HASH, sizeof(UNINIT_HASH)) ==
        0) {
      if (hash_pos != std::string::npos) {
        LOG_ERROR("Multiple occurrences of placeholder hash found");
        return false;
      }
      hash_pos = i;
    }
  }

  if (hash_pos == std::string::npos) {
    LOG_ERROR("Could not find placeholder hash in binary");
    return false;
  }

  //  Calculate the hash
  std::vector<uint8_t> calculated_hash(SHA256_DIGEST_LENGTH);
  if (!calculate_hash(text_module, rodata_module, calculated_hash)) {
    LOG_ERROR("Failed to calculate hash");
    return false;
  }


  //  Replace the placeholder with the calculated hash
  std::memcpy(binary_data.data() + hash_pos, calculated_hash.data(),
              calculated_hash.size());

  //  Write the modified binary
  std::ofstream output_file(output_path, std::ios::binary);
  if (!output_file) {
    LOG_ERROR("Failed to open output file: %s", output_path.c_str());
    return false;
  }

  if (!output_file.write(reinterpret_cast<char *>(binary_data.data()),
                         binary_data.size())) {
    LOG_ERROR("Failed to write file %s", output_path.c_str());
    return false;
  }

  LOG_INFO("Successfully injected hash at offset %zu", hash_pos);
  return true;
}

int main(int argc, char *argv[]) {
  std::vector<std::string> args;
  for (int i = 1; i < argc; i++) {
    args.push_back(argv[i]);
  }

  args_map_t args_map;
  args_list_t extra_args;

  if (!ParseKeyValueArguments(args_map, extra_args, args, kArguments)) {
    LOG_ERROR("Failed to parse arguments");
    print_usage();
    return 1;
  }

  // Get the input and output file paths
  std::string input_file, output_file;
  if (!GetString(&input_file, "-in-object", "", args_map) ||
      !GetString(&output_file, "-o", "", args_map)) {
    LOG_ERROR("Error getting file paths");
    print_usage();
    return 1;
  }

  // Get the apple flag
  bool is_apple = false;
  if (!GetBoolArgument(&is_apple, "-apple", args_map)) {
    LOG_ERROR("Error getting apple flag");
    print_usage();
    return 1;
  }

  // Display configuration
  LOG_INFO("Input file:  %s", input_file.c_str());
  LOG_INFO("Output file: %s", output_file.c_str());
  if (is_apple) {
    LOG_INFO("Platform: macOS");
  }

  return process(input_file, output_file, is_apple) ? 0 : 1;
}
