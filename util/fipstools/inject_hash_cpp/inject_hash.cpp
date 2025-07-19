#include <LIEF/LIEF.hpp>
#include <iostream>
#include <string>
#include <cstdlib>
#include <filesystem>
#include <fstream>

// Function to extract object from archive
bool extract_from_archive(const std::string& archive_path, const std::string& temp_dir) {
    std::string extract_cmd = "ar x " + archive_path + " -C " + temp_dir;
    return system(extract_cmd.c_str()) == 0;
}

// Function to create archive from object
bool create_archive(const std::string& archive_path, const std::string& object_path) {
    std::string create_cmd = "ar rcs " + archive_path + " " + object_path;
    return system(create_cmd.c_str()) == 0;
}

int main(int argc, char** argv) {
    std::cout << "\n=== C++ inject_hash starting ===" << std::endl;
    std::cout << "Testing LIEF integration..." << std::endl;

    const char* binary_path = nullptr;
    bool is_archive = false;

    for (int i = 1; i < argc - 1; i++) {
        if (strcmp(argv[i], "-in-object") == 0) {
            binary_path = argv[i + 1];
            break;
        }
        else if (strcmp(argv[i], "-in-archive") == 0) {
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
        // Create temporary directory
        std::string temp_dir = std::filesystem::temp_directory_path().string() + 
                             "/inject_hash_temp_" + std::to_string(std::rand());
        std::filesystem::create_directory(temp_dir);

        std::cout << "Extracting archive..." << std::endl;
        if (!extract_from_archive(binary_path, temp_dir)) {
            std::cerr << "❌ Failed to extract archive" << std::endl;
            return 1;
        }

        // There should be only one object file
        std::string object_file;
        for (const auto& entry : std::filesystem::directory_iterator(temp_dir)) {
            if (object_file.empty()) {
                object_file = entry.path().string();
            } else {
                std::cerr << "❌ Multiple files found in archive" << std::endl;
                return 1;
            }
        }

        // Parse the object file
        if (auto binary = LIEF::Parser::parse(object_file)) {
            std::cout << "✅ Successfully parsed object from archive: " << object_file << std::endl;
            
            // TODO: Process the object file here
            
            // Recreate the archive with modified object
            if (!create_archive(binary_path, object_file)) {
                std::cerr << "❌ Failed to create archive" << std::endl;
                return 1;
            }
        } else {
            std::cerr << "❌ Failed to parse object from archive" << std::endl;
            return 1;
        }

        // Cleanup
        std::filesystem::remove_all(temp_dir);
    } else {
        // Regular object file handling
        if (auto binary = LIEF::Parser::parse(binary_path)) {
            std::cout << "✅ LIEF parser successfully loaded: " << binary_path << std::endl;
        } else {
            std::cerr << "❌ LIEF parser failed to load: " << binary_path << std::endl;
            return 1;
        }
    }

    std::cout << "=== C++ inject_hash completed ===" << std::endl;
    return 0;
}
