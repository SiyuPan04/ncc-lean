param(
    [string]$LeanBin = ''
)

$ErrorActionPreference = 'Stop'
$projectRoot = $PSScriptRoot
$toolchain = (Get-Content -LiteralPath (Join-Path $projectRoot 'lean-toolchain') -Raw).Trim()
$expectedVersion = ($toolchain -split ':')[-1].TrimStart('v')

if ($LeanBin) {
    $lakeExe = Join-Path $LeanBin 'lake.exe'
} elseif (Get-Command lake -ErrorAction SilentlyContinue) {
    $lakeExe = (Get-Command lake).Source
} else {
    $toolchainFolder = $toolchain.Replace('/', '--').Replace(':', '---')
    $lakeExe = Join-Path $env:USERPROFILE ".elan\toolchains\$toolchainFolder\bin\lake.exe"
}
if (-not (Test-Path -LiteralPath $lakeExe)) {
    throw 'Lean/Lake was not found. Install elan, or pass -LeanBin with the matching toolchain bin directory.'
}

Push-Location $projectRoot
try {
    $leanVersion = & $lakeExe env lean --version
    if ($LASTEXITCODE -ne 0 -or $leanVersion -notmatch [regex]::Escape("version $expectedVersion,")) {
        throw "Expected Lean $expectedVersion; received: $leanVersion"
    }
    Write-Output $leanVersion
    & $lakeExe --wfail build
    if ($LASTEXITCODE -ne 0) { throw 'Lean build failed.' }

    # Do not silently leave a new mathematical module outside the root audit.
    $sourcePaths = @(Get-ChildItem -LiteralPath (Join-Path $projectRoot 'NCC') -Filter '*.lean' -File -Recurse)
    $modulePaths = @{'NCC' = (Join-Path $projectRoot 'NCC.lean')}
    foreach ($sourcePath in $sourcePaths) {
        $relativePath = [IO.Path]::GetRelativePath($projectRoot, $sourcePath.FullName)
        $moduleName = $relativePath -replace '\\', '.' -replace '/', '.' -replace '\.lean$', ''
        $modulePaths[$moduleName] = $sourcePath.FullName
    }
    $checkedModules = [Collections.Generic.HashSet[string]]::new()
    $pendingModules = [Collections.Generic.Queue[string]]::new()
    $pendingModules.Enqueue('NCC')
    while ($pendingModules.Count -gt 0) {
        $currentModule = $pendingModules.Dequeue()
        if (-not $checkedModules.Add($currentModule)) { continue }
        foreach ($sourceLine in (Get-Content -LiteralPath $modulePaths[$currentModule])) {
            if ($sourceLine -match '^import\s+(NCC(?:\.[A-Za-z0-9_]+)*)\s*$') {
                $importName = $Matches[1]
                if ($modulePaths.ContainsKey($importName)) { $pendingModules.Enqueue($importName) }
            }
        }
    }
    $unimportedModules = @($modulePaths.Keys | Where-Object { -not $checkedModules.Contains($_) })
    if ($unimportedModules.Count -gt 0) {
        throw ('Mathematical modules missing from NCC.lean: ' + ($unimportedModules -join ', '))
    }
    Write-Output "Root coverage passed for all $($sourcePaths.Count) NCC source files."

    & $lakeExe env lean Audit/Axioms.lean
    if ($LASTEXITCODE -ne 0) { throw 'Axiom audit failed.' }

    $paperPath = Join-Path $projectRoot '..\main.tex'
    $record = Get-Content -LiteralPath (Join-Path $projectRoot 'paper-manifest.json') -Raw | ConvertFrom-Json
    if (Test-Path -LiteralPath $paperPath) {
        $currentHash = (Get-FileHash -LiteralPath $paperPath -Algorithm SHA256).Hash
        if ($currentHash -ne $record.sha256) {
            Write-Warning 'main.tex has changed since the recorded baseline. Recheck the correspondence in STATUS.md.'
        }
    }
    Write-Output 'Build, source coverage, and axiom audit passed.'
} finally {
    Pop-Location
}
