#include <LIEF/LIEF.hpp>
#include <iostream>
#include <string>
#include <vector>
#include <tool/internal.h>

static const argument_t kArguments[] = {
    {"-in-object", kRequiredArgument, "Input object file path"},
    {"-o", kRequiredArgument, "Output file path"},
    {"-apple", kBooleanArgument, "Apple platform flag"},
    {"", kOptionalArgument, ""}  // Terminating element
};

static void print_usage() {
    std::cout << "Usage: inject_hash_cpp -o output_file -in-object input_file [-apple]" << std::endl;
    PrintUsage(kArguments);
}

int main(int argc, char** argv) {
    std::cout << "\n=== C++ inject_hash starting ===" << std::endl;

    // Convert argv to vector of strings, skipping program name (argv[0])
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
