// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// capture_hash runs another executable that has been linked with libcrypto. It expects the libcrypto to run the
// power-on self-tests and fail due to a fingerprint mismatch. capture_hash parses the output, takes the correct
// fingerprint value, and generates a new C file that contains the correct fingerprint which is used to build the
// final libcrypto.

#include <string>
#include <vector>
#include <sstream>
#include <iostream>
#include <io.h>
#include <cstring>
#include <errno.h>
#include <tool/internal.h>

#define LOG_ERROR(fmt, ...) fprintf(stderr, "Error: " fmt "\n", ##__VA_ARGS__)
#define LOG_INFO(fmt, ...) fprintf(stdout, fmt "\n", ##__VA_ARGS__)

const std::string LINE0 = "AWS-LC FIPS failure caused by:";
const std::string LINE1 = "FIPS integrity test failed.";
// This must match what is in crypto/fipsmodule/fips_shared_support.c
const std::string LINE2 = "Expected:   ae2cea2abda6f3ec977f9bf6949afc836827cba0a09f6b6fde52cde2cdff3180";
const int HASH_LEN = 64;

static const argument_t kArguments[] = {
    {"-in-executable", kRequiredArgument, "Input executable file path"},
    {"", kOptionalArgument, ""}  // Terminating element
};

static void print_usage() {
    LOG_INFO("Usage: capture_hash_cpp -in-executable <path>");
    PrintUsage(kArguments);
}

// Function declarations
static std::vector<std::string> split_string(const std::string& str, const std::string& delimiter);
static std::vector<std::string> split_by_space(const std::string& str);
static bool execute_command(const std::string& executable, std::string& output);

static std::vector<std::string> split_string(const std::string& str, const std::string& delimiter) {
    std::vector<std::string> tokens;
    size_t start = 0;
    size_t end = str.find(delimiter);
    
    while (end != std::string::npos) {
        tokens.push_back(str.substr(start, end - start));
        start = end + delimiter.length();
        end = str.find(delimiter, start);
    }
    
    tokens.push_back(str.substr(start));
    return tokens;
}

static std::vector<std::string> split_by_space(const std::string& str) {
    std::vector<std::string> tokens;
    std::istringstream iss(str);
    std::string token;
    
    while (iss >> token) {
        tokens.push_back(token);
    }
    
    return tokens;
}

static bool execute_command(const std::string& executable, std::string& output) {
    std::string command = executable + " 2>&1"; // Redirect stderr to stdout
    std::cerr << "Executing command: " << command << std::endl;
    char buffer[128];
    FILE* pipe = _popen(command.c_str(), "r");
    
    if (!pipe) {
        std::cerr << "Error: _popen() failed: " << strerror(errno) << std::endl;
        return false;
    }
    
    while (fgets(buffer, sizeof(buffer), pipe) != nullptr) {
        output += buffer;
    }
    std::cerr << "Raw command output:\n" << output << std::endl;
    
    int status = _pclose(pipe);
    bool succeeded = (status == 0);

    std::cerr << "Command exit status: " << status << std::endl;
    
    // Check if the command succeeded when it should have failed
    if (succeeded) {
        std::cerr << output;
        std::cerr << "Error: Executable did not fail as expected" << std::endl;
        return false;
    }
    
    return true;
}

int main(int argc, char* argv[]) {
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

    std::string executable;
    if (!GetString(&executable, "-in-executable", "", args_map)) {
        LOG_ERROR("Error getting executable path");
        print_usage();
        return 1;
    }


    std::string output;
    if (!execute_command(executable, output)) {
        return 1;
    }
    
    // Split output into lines - checking for both Windows (\r\n) and Unix (\n) line endings
    std::vector<std::string> lines;
    if (output.find("\r\n") != std::string::npos) {
        lines = split_string(output, "\r\n");
        std::cerr << "Found Windows-style line endings" << std::endl;
    } else {
        lines = split_string(output, "\n");
        std::cerr << "Found Unix-style line endings" << std::endl;
    }

    std::cerr << "Number of lines in output: " << lines.size() << std::endl;
    
    if (lines.size() != 6) {
        std::cerr << output;
        std::cerr << "Error: Expected 6 lines in output but got " << lines.size() << std::endl;
        return 1;
    }

    if (lines[0] != LINE0) {
        std::cerr << output;
        std::cerr << "Error: Expected \"" << LINE0 << "\" got \"" << lines[0] << "\"" << std::endl;
        return 1;
    }

    if (lines[1] != LINE1) {
        std::cerr << output;
        std::cerr << "Error: Expected \"" << LINE1 << "\" got \"" << lines[1] << "\"" << std::endl;
        return 1;
    }

    if (lines[2] != LINE2) {
        std::cerr << output;
        std::cerr << "Error: Expected \"" << LINE2 << "\" got \"" << lines[2] << "\"" << std::endl;
        return 1;
    }

    auto hash_parts = split_by_space(lines[3]);
    if (hash_parts.size() < 2) {
        std::cerr << output;
        std::cerr << "Error: Could not parse hash from line: " << lines[3] << std::endl;
        return 1;
    }
    
    std::string hash = hash_parts[1];
    std::cerr << "Found hash value: " << hash << std::endl;

    if (hash.length() != HASH_LEN) {
        std::cerr << output;
        std::cerr << "Error: Hash \"" << hash << "\" is " << hash.length() 
                  << " long, expected " << HASH_LEN << std::endl;
        return 1;
    }

    // Output the generated C code
    std::cout << "// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.\n"
              << "// SPDX-License-Identifier: Apache-2.0 OR ISC\n"
              << "// This file is generated by: 'capture_hash_cpp -in-executable " << executable << "'\n"
              << "#include <stdint.h>\n"
              << "const uint8_t BORINGSSL_bcm_text_hash[32] = {\n";

    for (size_t i = 0; i < hash.length(); i += 2) {
        std::cout << "0x" << hash.substr(i, 2) << ", ";
    }

    std::cout << "\n};\n";

    return 0;
}
