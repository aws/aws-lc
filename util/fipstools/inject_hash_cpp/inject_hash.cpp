#include <LIEF/LIEF.hpp>
#include <iostream>
#include <string>
#include <cstdlib>
#include <filesystem>

namespace fs = std::filesystem;

int main(int argc, char** argv) {
    std::cout << "\n=== C++ inject_hash starting ===" << std::endl;

    // Verify LIEF
    try {
        std::cout << "LIEF version: " << LIEF::version << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "LIEF error: " << e.what() << std::endl;
        return 1;
    }

    // Verify ar command
    if (system("ar --version") != 0) {
        std::cerr << "ar command not available" << std::endl;
        return 1;
    }

    const char* binary_path = nullptr;
    bool is_archive = false;

    for (int i = 1; i < argc - 1; i++) {
        if (strcmp(argv[i], "-in-archive") == 0) {
            binary_path = argv[i + 1];
            is_archive = true;
            break;
        }
    }

    if (!binary_path) {
        std::cerr << "❌ No binary path provided" << std::endl;
        return 1;
    }

    if (is_archive) {
        std::cout << "Testing archive extraction and parsing..." << std::endl;
        
        try {
            // Create temp directory
            fs::path temp_dir = fs::temp_directory_path() / 
                              fs::path("inject_hash_temp_" + std::to_string(std::rand()));
            fs::create_directory(temp_dir);
            std::cout << "Created temp dir: " << temp_dir << std::endl;
            
            // Extract archive
            std::string extract_cmd = "cd " + temp_dir.string() + " && ar x " + binary_path;
            std::cout << "Running: " << extract_cmd << std::endl;
            if (system(extract_cmd.c_str()) != 0) {
                std::cerr << "❌ Failed to extract archive" << std::endl;
                fs::remove_all(temp_dir);
                return 1;
            }

            // Find extracted file
            std::string extracted_file;
            for (const auto& entry : fs::directory_iterator(temp_dir)) {
                if (extracted_file.empty()) {
                    extracted_file = entry.path().string();
                    std::cout << "Found file: " << extracted_file << std::endl;
                } else {
                    std::cerr << "❌ Multiple files found in archive" << std::endl;
                    fs::remove_all(temp_dir);
                    return 1;
                }
            }

            if (extracted_file.empty()) {
                std::cerr << "❌ No files found in archive" << std::endl;
                fs::remove_all(temp_dir);
                return 1;
            }

            // Try parsing
            if (auto binary = LIEF::Parser::parse(extracted_file)) {
                std::cout << "✅ Successfully parsed extracted file" << std::endl;
            } else {
                std::cerr << "❌ Failed to parse extracted file" << std::endl;
                fs::remove_all(temp_dir);
                return 1;
            }

            // Cleanup
            fs::remove_all(temp_dir);

        } catch (const fs::filesystem_error& e) {
            std::cerr << "Filesystem error: " << e.what() << std::endl;
            return 1;
        } catch (const std::exception& e) {
            std::cerr << "Error: " << e.what() << std::endl;
            return 1;
        }
    }

    std::cout << "=== C++ inject_hash completed ===" << std::endl;
    return 0;
}
