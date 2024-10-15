#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <iterator>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

// Function to find and replace a byte sequence in a vector of bytes.
static int findAndReplace(std::vector<unsigned char>& data, const std::vector<unsigned char>& searchSeq, const std::vector<unsigned char>& replaceSeq) {
    auto it = std::search(data.begin(), data.end(), searchSeq.begin(), searchSeq.end());

    if (it != data.end()) {
        std::copy(replaceSeq.begin(), replaceSeq.end(), it);
        return 1;
    }

    return 0;
}

static std::vector<unsigned char> hexStringToBytes(const std::string& hex) {
    std::vector<unsigned char> byteArray;

    // Iterate over the hex string two characters at a time
    for (size_t i = 0; i < hex.length(); i += 2) {
        // Convert the two hex characters to a byte
        std::string byteString = hex.substr(i, 2);
        unsigned char byte = static_cast<unsigned char>(strtol(byteString.c_str(), nullptr, 16));
        byteArray.push_back(byte);
    }

    return byteArray;
}

int main(int argc, char* argv[]) {
    if (argc != 3) {
        std::cerr << "Usage: " << argv[0] << " libcryptoFile fipsEmptyMainFile" << std::endl;
        return 1;
    }
    const std::string libcryptoFile = argv[1];
    const std::string fipsEmptyMainFile = argv[2];

    // We execute the fipsEmptyMain program to catch its output
    // which contains the expected and calculated hash value.

    // Make sure stderr is redirected to stdout.
    std::string command = fipsEmptyMainFile + " 2>&1";

    // Execute the comand and get the output.
    std::array<char, 1000> buffer;
    std::string fipsEmptyMainOutput;
#if defined(_WIN32)
    std::unique_ptr<FILE, decltype(&_pclose)> pipe(_popen(command, "r"), _pclose);
#else
    std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(command.c_str(), "r"), pclose);
#endif
    if (!pipe) {
        std::cerr << "popen() failed!" << std::endl;
        return 1;
    }
    while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
        fipsEmptyMainOutput += buffer.data();
    }

    // The output should contain three lines:
    //   FIPS integrity test failed.
    //   Expected:    xyz...
    //   Calculated:  asd...
    if (fipsEmptyMainOutput.find("FIPS integrity test failed.") == std::string::npos ||
        fipsEmptyMainOutput.find("Expected") == std::string::npos ||
        fipsEmptyMainOutput.find("Calculated") == std::string::npos) {
        std::cerr << "fips_empty_main returned unexpected output!" << std::endl;
        return 1;
    }
    std::istringstream iss(fipsEmptyMainOutput);
    std::string label, expectedHash, calculatedHash;
    std::getline(iss, label); // skip the first line.
    iss >> label; iss >> expectedHash;
    iss >> label; iss >> calculatedHash;

    // Convert the hex strings representing hash values to bytes.
    std::vector<unsigned char> expectedHashBytes = hexStringToBytes(expectedHash);
    std::vector<unsigned char> calculatedHashBytes = hexStringToBytes(calculatedHash);

    // Find the expected and replace it with the calculated hash.
    std::ifstream input(libcryptoFile, std::ios::binary);
    if (!input) {
        std::cerr << "Error: Unable to open the binary!" << std::endl;
        return 1;
    }

    // Read the input file into a vector of bytes.
    std::vector<unsigned char> data((std::istreambuf_iterator<char>(input)), std::istreambuf_iterator<char>());
    input.close();

    if (!findAndReplace(data, expectedHashBytes, calculatedHashBytes)) {
        std::cerr << "Error: didn't find the expected hash value in the binary!" << std::endl;
        return 1;
    }

    // Write the modified data to the output binary file.
    std::ofstream output(libcryptoFile, std::ios::binary);
    if (!output) {
        std::cerr << "Error: Unable to open output file!" << std::endl;
        return 1;
    }
    output.write(reinterpret_cast<const char*>(data.data()), data.size());
    output.close();

    return 0;
}
