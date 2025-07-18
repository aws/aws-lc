#include <LIEF/LIEF.hpp>
#include <iostream>
#include <string>

int main(int argc, char** argv) {
    std::cout << "\n=== C++ inject_hash starting ===" << std::endl;
    std::cout << "Testing LIEF integration..." << std::endl;

    // only for testing purposes
    const char* binary_path = nullptr;
    for (int i = 1; i < argc - 1; i++) {
        if (strcmp(argv[i], "-in-object") == 0) {
            binary_path = argv[i + 1];
            break;
        }
    }

    if (binary_path) {
        if (auto binary = LIEF::Parser::parse(binary_path)) {
            std::cout << "✅ LIEF parser successfully loaded: " << binary_path << std::endl;
        } else {
            std::cerr << "❌ LIEF parser failed to load: " << binary_path << std::endl;
            return 1;
        }
    } else {
        std::cerr << "❌ No binary path provided" << std::endl;
        return 1;
    }

    std::cout << "=== C++ inject_hash completed ===" << std::endl;
    return 0;
}


