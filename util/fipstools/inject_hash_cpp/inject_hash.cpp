// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <LIEF/LIEF.hpp>
#include <iostream>
#include <fstream>
#include <vector>
#include <memory>
#include <cstring>
#include <getopt.h>
#include <openssl/hmac.h> 
#include <tool/internal.h>
#include <string>
#include <inttypes.h> 


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
  std::cout
      << "Usage: inject_hash_cpp -o output_file -in-object input_file [-apple]"
      << std::endl;
  PrintUsage(kArguments);
}

class InjectHash {
private:
    // Placeholder hash pattern from fips_shared_support.c
    static constexpr uint8_t UNINIT_HASH[32] = {
        0xae, 0x2c, 0xea, 0x2a, 0xbd, 0xa6, 0xf3, 0xec, 
        0x97, 0x7f, 0x9b, 0xf6, 0x94, 0x9a, 0xfc, 0x83, 
        0x68, 0x27, 0xcb, 0xa0, 0xa0, 0x9f, 0x6b, 0x6f, 
        0xde, 0x52, 0xcd, 0xe2, 0xcd, 0xff, 0x31, 0x80
    };

    std::string input_path_;
    std::string output_path_;
    bool is_apple_;

    // Convert a size to little-endian representation
    static void size_to_little_endian(size_t size, uint8_t* result) {
        for (int i = 0; i < 8; i++) {
            result[i] = (size >> (i * 8)) & 0xFF;
        }
    }

    // Extract module content using LIEF for Apple platforms
    bool extract_apple_modules(std::vector<uint8_t>& text_module, std::vector<uint8_t>& rodata_module) {
            // Parse the binary with LIEF
            auto binary = LIEF::MachO::Parser::parse(input_path_);
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
            const auto* text_start = macho->get_symbol("_BORINGSSL_bcm_text_start");
            if (!text_start) {
                LOG_ERROR("Could not find BORINGSSL_bcm_text_start symbol");
            }
            const auto* text_end = macho->get_symbol("_BORINGSSL_bcm_text_end");
            if (!text_end) {
                LOG_ERROR("Could not find BORINGSSL_bcm_text_end symbol");
            }
            const auto* rodata_start = macho->get_symbol("_BORINGSSL_bcm_rodata_start");
            const auto* rodata_end = macho->get_symbol("_BORINGSSL_bcm_rodata_end");


            // Find the sections containing these symbols
            const LIEF::MachO::Section* text_section = nullptr;
            const LIEF::MachO::Section* rodata_section = nullptr;

           const auto* text_segment = macho->get_segment("__TEXT");
            if (!text_segment) {
                LOG_ERROR("Could not find __TEXT segment");
                return false;
            }

            for (const auto& section : text_segment->sections()) {
                if (section.name() == "__text") {
                    text_section = &section;
                    LOG_INFO("Found __text section at virtual address: 0x%" PRIx64, section.virtual_address());
                }
                else if (section.name() == "__const") {
                    rodata_section = &section;
                    LOG_INFO("Found __const section at virtual address: 0x%" PRIx64, section.virtual_address());
                }
            }

            if (!text_section) {
                LOG_ERROR("Could not locate __text section");
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
            std::memcpy(text_module.data(), content.data() + text_start_offset, text_module.size());

            // Extract rodata module if present
            if (rodata_section && rodata_start && rodata_end) {
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
                std::memcpy(rodata_module.data(), rodata_content.data() + rodata_start_offset, rodata_module.size());
            }
            else {
                if ((rodata_start == nullptr) != (rodata_section == nullptr)) {
                LOG_ERROR("rodata start marker inconsistent with rodata section presence");
                return false;
                }
                if ((rodata_start != nullptr) != (rodata_end != nullptr)) {
                    LOG_ERROR("rodata marker presence inconsistent");
                    return false;
                }
                rodata_module.clear();
                }

            return true;
    }

    bool extract_linux_modules(std::vector<uint8_t>& text_module, std::vector<uint8_t>& rodata_module) {
            // Parse the binary with LIEF
            auto binary = LIEF::ELF::Parser::parse(input_path_);
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
            const auto* text_start = elf->get_symbol("BORINGSSL_bcm_text_start");
            if (!text_start) {
                LOG_ERROR("Could not find BORINGSSL_bcm_text_start symbol");
            }
            const auto* text_end = elf->get_symbol("BORINGSSL_bcm_text_end");
            if (!text_end) {
                LOG_ERROR("Could not find BORINGSSL_bcm_text_end symbol");
            }
            const auto* rodata_start = elf->get_symbol("BORINGSSL_bcm_rodata_start");
            const auto* rodata_end = elf->get_symbol("BORINGSSL_bcm_rodata_end");


            // Find the sections containing these symbols
            const LIEF::ELF::Section* text_section = nullptr;
            const LIEF::ELF::Section* rodata_section = nullptr;

            for (const auto& section : elf->sections()) {
                if (section.name() == ".text") {
                    text_section = &section;
                    LOG_INFO("Found .text section at virtual address: 0x%" PRIx64, section.virtual_address());
                }
                if (section.name() == ".rodata") {
                    rodata_section = &section;
                    LOG_INFO("Found .rodata section at virtual address: 0x%" PRIx64, section.virtual_address());
                }
            }

            if (!text_section) {
                LOG_ERROR("Could not locate .text section");
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
            std::memcpy(text_module.data(), content.data() + text_start_offset, text_module.size());

            // Extract rodata module if present
            if (rodata_section && rodata_start && rodata_end) {
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
                std::memcpy(rodata_module.data(), rodata_content.data() + rodata_start_offset, rodata_module.size());
            }
            else {
                if ((rodata_start == nullptr) != (rodata_section == nullptr)) {
                LOG_ERROR("rodata start marker inconsistent with rodata section presence");
                return false;
                }
                if ((rodata_start != nullptr) != (rodata_end != nullptr)) {
                    LOG_ERROR("rodata marker presence inconsistent");
                    return false;
                }
                rodata_module.clear();
                }

            return true;
    }

    // Calculate HMAC hash
    std::vector<uint8_t> calculate_hash(const std::vector<uint8_t>& text_module,
                                       const std::vector<uint8_t>& rodata_module) {
        std::vector<uint8_t> hash_result(32); // SHA256 size
        uint8_t zero_key[64] = {0};
        uint8_t length_bytes[8];
        
        HMAC_CTX* ctx = HMAC_CTX_new();
        if (!ctx) {
            LOG_ERROR("Failed to create HMAC context");
            return hash_result;
        }

        if (!HMAC_Init_ex(ctx, zero_key, sizeof(zero_key), EVP_sha256(), nullptr)) {
            LOG_ERROR("HMAC_Init failed");
            HMAC_CTX_free(ctx);
            return hash_result;
        }

        // Add text module size and content
        size_to_little_endian(text_module.size(), length_bytes);
        if (!HMAC_Update(ctx, length_bytes, sizeof(length_bytes)) ||
            !HMAC_Update(ctx, text_module.data(), text_module.size())) {
            LOG_ERROR("HMAC_Update failed for text module");
            HMAC_CTX_free(ctx);
            return hash_result;
        }

        // Add rodata module size and content if present
        if (!rodata_module.empty()) {
            size_to_little_endian(rodata_module.size(), length_bytes);
            if (!HMAC_Update(ctx, length_bytes, sizeof(length_bytes)) ||
                !HMAC_Update(ctx, rodata_module.data(), rodata_module.size())) {
                LOG_ERROR("HMAC_Update failed for rodata module");
                HMAC_CTX_free(ctx);
                return hash_result;
            }
        }

        unsigned int hash_len;
        if (!HMAC_Final(ctx, hash_result.data(), &hash_len)) {
            LOG_ERROR("HMAC_Final failed");
            HMAC_CTX_free(ctx);
            return hash_result;
        }

        HMAC_CTX_free(ctx);

        // Print calculated hash for reference
        LOG_INFO("Calculated hash: ");
        for (unsigned int i = 0; i < hash_len; i++) {
            printf("%02X", hash_result[i]);
        }
        printf("\n");

        return hash_result;
    }

public:
    InjectHash(const std::string& input_path, const std::string& output_path, bool is_apple)
        : input_path_(input_path), output_path_(output_path), is_apple_(is_apple) {} // the constructor initializes the input and output paths and the platform flag

    bool process() {
        // Read the input binary file
        std::ifstream input_file(input_path_, std::ios::binary | std::ios::ate); // Open the file in binary mode and move to the end to get size (the ate pointer gets to the end of the file)
        if (!input_file) {
            LOG_ERROR("Failed to open input file: %s", input_path_.c_str());
            return false;
        }
        
        size_t file_size = input_file.tellg();
        input_file.seekg(0, std::ios::beg); // Move back to the beginning of the file to read its content
        
        // ??
        std::vector<uint8_t> binary_data(file_size);
        if (!input_file.read(reinterpret_cast<char*>(binary_data.data()), file_size)) {
            LOG_ERROR("Failed to read file %s", input_path_.c_str());
            return false;
        }

        //  Extract module content based on platform
        std::vector<uint8_t> text_module, rodata_module;
        if (is_apple_) {
            if (!extract_apple_modules(text_module, rodata_module)) {
                LOG_ERROR("Failed to extract modules from Apple binary");
                return false;
            }
        } else{
            if (!extract_linux_modules(text_module, rodata_module)) {
                LOG_ERROR("Failed to extract modules from Linux binary");
                return false;
            }
        }

        //  Find the placeholder hash in the binary
        size_t hash_pos = std::string::npos;
        for (size_t i = 0; i <= binary_data.size() - sizeof(UNINIT_HASH); i++) {
            if (std::memcmp(binary_data.data() + i, UNINIT_HASH, sizeof(UNINIT_HASH)) == 0) {
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
        auto calculated_hash = calculate_hash(text_module, rodata_module);

        //  Replace the placeholder with the calculated hash
        std::memcpy(binary_data.data() + hash_pos, calculated_hash.data(), calculated_hash.size());

        //  Write the modified binary
        std::ofstream output_file(output_path_, std::ios::binary);
        if (!output_file) {
            LOG_ERROR("Failed to open output file: %s", output_path_.c_str());
            return false;
        }
        
        if (!output_file.write(reinterpret_cast<char*>(binary_data.data()), binary_data.size())) {
            LOG_ERROR("Failed to write file %s", output_path_.c_str());
            return false;
        }

        LOG_INFO("Successfully injected hash at offset %zu", hash_pos);
        return true;
    }
};

constexpr uint8_t InjectHash::UNINIT_HASH[32];

int main(int argc, char* argv[]) {
    std::vector<std::string> args;
    for (int i = 1; i < argc; i++) {
        args.push_back(argv[i]);
    }

    args_map_t args_map;
    args_list_t extra_args;

    if (!ParseKeyValueArguments(args_map, extra_args, args, kArguments)) {
        std::cerr << "❌ Failed to parse arguments" << std::endl;
        print_usage();
        return 1;
    }

    // Get the input and output file paths
    std::string input_file, output_file;
    if (!GetString(&input_file, "-in-object", "", args_map) ||
        !GetString(&output_file, "-o", "", args_map)) {
        std::cerr << "❌ Error getting file paths" << std::endl;
        print_usage();
        return 1;
    }

    // Get the apple flag
    bool is_apple = false;
    GetBoolArgument(&is_apple, "-apple", args_map);

    // Display configuration
    std::cout << "Input file:  " << input_file << std::endl;
    std::cout << "Output file: " << output_file << std::endl;
    if (is_apple) {
        std::cout << "Platform: macOS" << std::endl;
    }

    InjectHash injector(input_file, output_file, is_apple);
    return injector.process() ? 0 : 1;
}
