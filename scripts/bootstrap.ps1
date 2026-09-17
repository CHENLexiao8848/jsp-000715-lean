param()
$ErrorActionPreference = 'Stop'
$jspRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $jspRoot
# Lake reads the checked-in manifest and fetches its exact pinned dependencies.
& lake exe cache get
if ($LASTEXITCODE -ne 0) { throw 'Fetching pinned Mathlib dependencies/cache failed.' }
Write-Output 'Pinned Mathlib cache ready. No external problem proof is needed.'
