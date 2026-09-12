$ErrorActionPreference = 'Stop'
$repositoryRoot = Split-Path $PSScriptRoot
Push-Location $repositoryRoot
try {
    $trackedFiles = @(& git ls-files)
    if ($LASTEXITCODE -ne 0 -or $trackedFiles.Count -eq 0) {
        throw 'No tracked repository files were found.'
    }
    $issues = [Collections.Generic.List[string]]::new()
    $macUserPattern = '/' + 'Users/' + '[^/\s]+/'
    foreach ($relativePath in $trackedFiles) {
        if ($relativePath -match '^(\.lake|tmp|\.git)/' -or
            $relativePath -match '(^|/)(\.env(?:\..*)?|[^/]+\.(pem|key))$') {
            $issues.Add("Excluded file is tracked: $relativePath")
            continue
        }
        $fileText = [IO.File]::ReadAllText((Join-Path $repositoryRoot $relativePath))
        if ($fileText -match '[\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff]' -or
            $relativePath -match '[\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff]') {
            $issues.Add("Non-English CJK text: $relativePath")
        }
        if ($fileText -match '(?i)[A-Z]:[\\/]Users[\\/]' -or
            $fileText -match $macUserPattern) {
            $issues.Add("Machine-specific user path: $relativePath")
        }
        if ($fileText -match 'gh[pousr]_[A-Za-z0-9]{30,}' -or
            $fileText -match 'github_pat_[A-Za-z0-9_]{30,}' -or
            $fileText -match '-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----') {
            $issues.Add("Potential credential: $relativePath")
        }
    }
    if ($issues.Count -gt 0) {
        $issues | ForEach-Object { Write-Output $_ }
        throw 'Repository checks failed; file contents have not been printed.'
    }
    Write-Output "Repository checks passed for $($trackedFiles.Count) tracked files."
} finally {
    Pop-Location
}
