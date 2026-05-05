#!/usr/bin/env pwsh
# Run one Lean file without letting a non-zero Lean exit scramble an interactive terminal.
# The script always prints LEAN_EXIT=<code>; callers should inspect that marker.

param(
    [Parameter(Mandatory = $true)]
    [string]$File,

    [switch]$Json
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Continue"
if (Get-Variable PSNativeCommandUseErrorActionPreference -ErrorAction SilentlyContinue) {
    $PSNativeCommandUseErrorActionPreference = $false
}

$repoRoot = (git -C $PSScriptRoot rev-parse --show-toplevel 2>$null) ?? (Resolve-Path "$PSScriptRoot/../../../").Path
$elanBin = Join-Path $env:USERPROFILE ".elan\bin"
if (Test-Path $elanBin) {
    $env:PATH = "$elanBin;$env:PATH"
}

Push-Location $repoRoot
try {
    if (-not (Test-Path -LiteralPath $File)) {
        [Console]::WriteLine("LEAN_FILE_NOT_FOUND=$File")
        [Console]::WriteLine("LEAN_EXIT=1")
        $global:LASTEXITCODE = 0
        return
    }

    $leanArgs = @("env", "lean")
    if ($Json) { $leanArgs += "--json" }
    $leanArgs += $File

    $output = & lake @leanArgs 2>&1
    $code = $LASTEXITCODE

    foreach ($line in $output) {
        [Console]::WriteLine($line.ToString())
    }
    [Console]::WriteLine("LEAN_EXIT=$code")
    $global:LASTEXITCODE = 0
} finally {
    Pop-Location
}
