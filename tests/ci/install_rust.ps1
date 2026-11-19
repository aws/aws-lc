# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# rust-phase1 CI probe (not for merge): install_rust.sh for Windows containers,
# which have no bash. A failure only warns.

$cargoBin = Join-Path $env:USERPROFILE '.cargo\bin'
$env:PATH = "$cargoBin;$env:PATH"
try {
  if (-not (Get-Command rustup -ErrorAction SilentlyContinue)) {
    # Windows PowerShell 5.1 may not offer TLS 1.2, which win.rustup.rs needs.
    [Net.ServicePointManager]::SecurityProtocol = [Net.ServicePointManager]::SecurityProtocol -bor [Net.SecurityProtocolType]::Tls12
    $arch = if ($env:PROCESSOR_ARCHITECTURE -eq 'ARM64') { 'aarch64' } else { 'x86_64' }
    $init = Join-Path $env:TEMP 'rustup-init.exe'
    Invoke-WebRequest -UseBasicParsing -Uri "https://win.rustup.rs/$arch" -OutFile $init
    & $init -y --no-modify-path --profile minimal --default-toolchain stable
    if ($LASTEXITCODE -ne 0) { throw "rustup-init exited with $LASTEXITCODE" }
  }
  rustup component add llvm-tools
  if ($LASTEXITCODE -ne 0) { throw "rustup component add llvm-tools exited with $LASTEXITCODE" }
  rustc --version
} catch {
  Write-Host "::warning title=ENABLE_RUST::install_rust.ps1: $_"
}
exit 0
