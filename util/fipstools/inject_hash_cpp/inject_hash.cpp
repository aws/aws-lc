#include <LIEF/LIEF.hpp>
#include <iostream>
#include <string>
#include <cstring>

static void print_usage() {
    std::cout << "Usage: inject_hash_cpp -o output_file -in-object input_file [-apple]" << std::endl;
}

int main(int argc, char** argv) {
    std::cout << "\n=== C++ inject_hash starting ===" << std::endl;

    // Parse command line arguments
    const char* input_file = nullptr;
    const char* output_file = nullptr;
    bool is_apple = false;

    for (int i = 1; i < argc - 1; i++) {
        if (strcmp(argv[i], "-in-object") == 0) {
            input_file = argv[i + 1];
            i++; // Skip next argument
        }
        else if (strcmp(argv[i], "-o") == 0) {
            output_file = argv[i + 1];
            i++; // Skip next argument
        }
        else if (strcmp(argv[i], "-apple") == 0) {
            is_apple = true;
        }
    }

    // Validate arguments
    if (!input_file || !output_file) {
        std::cerr << "❌ Missing required arguments" << std::endl;
        print_usage();
        return 1;
    }

    std::cout << "Input file:  " << input_file << std::endl;
    std::cout << "Output file: " << output_file << std::endl;
    if (is_apple) {
        std::cout << "Platform: macOS" << std::endl;
    }

    // Parse binary
    std::cout << "\nParsing binary..." << std::endl;
    if (auto binary = LIEF::Parser::parse(input_file)) {
        std::cout << "✅ LIEF parser successfully loaded: " << input_file << std::endl;
        

        // TODO: Add hash calculation and injection
        
    } else {
        std::cerr << "❌ LIEF parser failed to load: " << input_file << std::endl;
        return 1;
    }

    std::cout << "=== C++ inject_hash completed ===" << std::endl;
    return 0;
}

