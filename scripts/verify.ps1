param()
$ErrorActionPreference = 'Stop'
$jspRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $jspRoot
$jspLogs = Join-Path $jspRoot 'artifacts/independent-verification'
New-Item -ItemType Directory -Force -Path $jspLogs | Out-Null
$jspResults = [Collections.Generic.List[object]]::new()
function Save-JspResults {
  $jspResults | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath (Join-Path $jspLogs 'results.json') -Encoding utf8
}
function Invoke-JspLake([string]$Name, [string[]]$LakeArgs) {
  $jspLog = Join-Path $jspLogs ($Name + '.log')
  & lake @LakeArgs *> $jspLog
  $jspCode = $LASTEXITCODE
  $jspResults.Add([ordered]@{ name=$Name; command=('lake ' + ($LakeArgs -join ' ')); exitCode=$jspCode; log=$jspLog })
  Save-JspResults
  if ($jspCode -ne 0) { Get-Content -LiteralPath $jspLog -Tail 25; throw ($Name + ' failed: ' + $jspCode) }
  Write-Output ($Name + ' passed')
}
# Resolve the actual local import closure, including audits.
$jspVisited = [Collections.Generic.HashSet[string]]::new()
$jspModules = [Collections.Generic.List[string]]::new()
$jspProofs = [Collections.Generic.List[string]]::new()
function Add-JspModule([string]$Module) {
  if (-not $jspVisited.Add($Module)) { return }
  $jspPath = $Module.Replace('.', '/') + '.lean'
  if (-not (Test-Path -LiteralPath $jspPath)) { throw ('Missing local module ' + $Module) }
  $jspText = Get-Content -LiteralPath $jspPath -Raw
  foreach ($jspLine in [IO.File]::ReadAllLines((Join-Path $jspRoot $jspPath))) {
    $jspLine = $jspLine.Trim()
    if (-not ($jspLine -match '^(?:(?:public|private|meta)[ ]+)*import(?:[ ]|$)')) { continue }
    $jspMatch = [regex]::Match($jspLine, '^import[ ]+([A-Za-z0-9_.]+)$')
    if (-not $jspMatch.Success) { throw ('Unsupported import syntax in ' + $jspPath + ': ' + $jspLine) }
    $jspImport = $jspMatch.Groups[1].Value
    if ($jspImport -eq 'JSP715' -or $jspImport.StartsWith('JSP715.')) { Add-JspModule $jspImport }
    elseif (-not $jspImport.StartsWith('Mathlib.')) { throw ('Unexpected dependency ' + $jspImport + ' in ' + $jspPath) }
  }
  $jspProofs.Add($jspPath)
  if ($Module -ne 'Audit' -and $Module -ne 'JSP715') { $jspModules.Add($Module) }
}
Add-JspModule 'JSP715'
Add-JspModule 'Audit'
$jspModules | Set-Content -LiteralPath (Join-Path $jspLogs 'local-import-closure.txt')
$jspSnapshotFiles = @($jspProofs) + @('lean-toolchain','lakefile.toml','lake-manifest.json','scripts/bootstrap.ps1','scripts/verify.ps1')
$jspBeforeHashes = @{}
foreach ($jspFile in $jspSnapshotFiles) { $jspBeforeHashes[$jspFile] = (Get-FileHash -LiteralPath $jspFile -Algorithm SHA256).Hash }
Invoke-JspLake 'lake-build' @('build')
Invoke-JspLake 'audit-module-build' @('build','JSP715.CRTAudit','JSP715.DifferenceAudit')
Invoke-JspLake 'axioms-signatures' @('env','lean','-j1','Audit.lean')
$jspAxiomText = Get-Content -LiteralPath (Join-Path $jspLogs 'axioms-signatures.log') -Raw
$jspAudits = [regex]::Matches($jspAxiomText, "'([^']+)' depends on axioms:[ ]*[[](.*)[]]")
$jspExpected = [regex]::Matches((Get-Content -LiteralPath 'Audit.lean' -Raw), '(?m)^#print axioms[ ]+([A-Za-z0-9_.]+)')
if ($jspExpected.Count -eq 0) { throw 'The root axiom audit is empty.' }
foreach ($jspExpectedItem in $jspExpected) {
  $jspName = $jspExpectedItem.Groups[1].Value
  if (-not ($jspAudits | Where-Object { $_.Groups[1].Value -eq $jspName })) { throw ('Missing axiom audit for ' + $jspName) }
}
foreach ($jspAudit in $jspAudits) {
  foreach ($jspAxiom in ($jspAudit.Groups[2].Value -split ',[ ]*')) {
    if ($jspAxiom -and $jspAxiom -notin @('propext','Classical.choice','Quot.sound')) { throw ('Unexpected axiom ' + $jspAxiom) }
  }
}
$jspResults.Add([ordered]@{name='axiom-allowlist';exitCode=0;declarations=$jspExpected.Count;allowed=@('propext','Classical.choice','Quot.sound')})
Save-JspResults
# Replay each local module sequentially against its imported environment.
foreach ($jspModule in $jspModules) {
  Invoke-JspLake ('kernel-' + $jspModule) @('env','leanchecker','--verbose',$jspModule)
}
& rg -n '\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool|trustCompiler|implemented_by)\b|^import[ ]+(ErdosProblems|Mathlib[ ]*$)' @jspProofs *> (Join-Path $jspLogs 'proof-token-scan.log')
$jspScanCode = $LASTEXITCODE
if ($jspScanCode -ne 1) { throw ('Proof token scan found a forbidden token or failed: ' + $jspScanCode) }
$jspResults.Add([ordered]@{name='proof-token-scan';exitCode=0;rgExitCode=$jspScanCode;meaning='No matches in the full local proof closure'})
& rg -n 'sorry|admit|axiom' JSP715 Audit.lean docs README.md *> (Join-Path $jspLogs 'repository-text-scan.log')
if ($LASTEXITCODE -gt 1) { throw 'Repository text scan failed.' }
& lake env lean --version *> (Join-Path $jspLogs 'lean-version.log')
if ($LASTEXITCODE -ne 0) { throw 'Lean version command failed.' }
if ((Get-Content -LiteralPath (Join-Path $jspLogs 'lean-version.log') -Raw) -notmatch 'version 4[.]34[.]0,') { throw 'Unexpected Lean version.' }
& git -C .lake/packages/mathlib rev-parse HEAD *> (Join-Path $jspLogs 'mathlib-commit.log')
if ($LASTEXITCODE -ne 0) { throw 'Mathlib commit command failed.' }
if ((Get-Content -LiteralPath (Join-Path $jspLogs 'mathlib-commit.log') -Raw).Trim() -ne '5ed2965256430c3649e86755f9576b54eca72435') { throw 'Unexpected Mathlib commit.' }
& git -C .lake/packages/mathlib status --short *> (Join-Path $jspLogs 'mathlib-status.log')
if ($LASTEXITCODE -ne 0) { throw 'Mathlib status command failed.' }
if ((Get-Content -LiteralPath (Join-Path $jspLogs 'mathlib-status.log') -Raw)) { throw 'Mathlib dependency is modified.' }
$jspResults.Add([ordered]@{name='pinned-environment';exitCode=0;meaning='Lean 4.34.0 and clean pinned Mathlib verified'})
$jspHashes = foreach ($jspFile in $jspSnapshotFiles) {
  $jspDigest = Get-FileHash -Algorithm SHA256 -LiteralPath $jspFile
  if ($jspBeforeHashes[$jspFile] -ne $jspDigest.Hash) { throw ('Source changed during verification: ' + $jspFile) }
  [ordered]@{path=$jspFile;sha256=$jspDigest.Hash.ToLowerInvariant()}
}
$jspHashes | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath (Join-Path $jspLogs 'hashes.json') -Encoding utf8
$jspResults.Add([ordered]@{name='source-stability';exitCode=0;meaning='All proof and build files unchanged throughout verification'})
Save-JspResults
Write-Output 'All checks completed. Full evidence: artifacts/independent-verification/'



