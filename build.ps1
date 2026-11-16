# Builds dist\GW2Monitor.exe – only needs the "Visual Studio Build Tools" (C# compiler).
# Usage:  powershell -ExecutionPolicy Bypass -File build.ps1
$ErrorActionPreference = 'Stop'
$root = $PSScriptRoot

$csc = @(
    "${env:ProgramFiles(x86)}\Microsoft Visual Studio\*\*\MSBuild\Current\Bin\Roslyn\csc.exe",
    "$env:ProgramFiles\Microsoft Visual Studio\*\*\MSBuild\Current\Bin\Roslyn\csc.exe"
) | ForEach-Object { Get-ChildItem $_ -ErrorAction SilentlyContinue } | Select-Object -First 1 -ExpandProperty FullName
if (-not $csc) { throw "Roslyn csc.exe not found. Please install 'Visual Studio Build Tools' with C# support." }

$fw   = "$env:WINDIR\Microsoft.NET\Framework64\v4.0.30319"
$obj  = Join-Path $root 'obj'
$dist = Join-Path $root 'dist'
New-Item -ItemType Directory -Force $obj, $dist | Out-Null

# 1) Generate the icon
& $csc -nologo -target:exe "-out:$obj\MakeIcon.exe" -r:System.Drawing.dll "$root\tools\MakeIcon.cs" "$root\src\IconArt.cs"
if ($LASTEXITCODE -ne 0) { throw "Could not build MakeIcon" }
& "$obj\MakeIcon.exe" "$obj\app.ico"
if ($LASTEXITCODE -ne 0) { throw "Could not generate the icon" }

# 2) Build the app
$refs = @(
    'System.dll', 'System.Core.dll', 'System.Xaml.dll', 'System.Xml.dll', 'System.Drawing.dll',
    'System.Windows.Forms.dll', 'System.Net.Http.dll', 'System.Web.Extensions.dll',
    "$fw\WPF\PresentationCore.dll", "$fw\WPF\PresentationFramework.dll", "$fw\WPF\WindowsBase.dll"
)
$cscArgs = @(
    '-nologo', '-target:winexe', '-optimize+', '-langversion:latest', '-codepage:65001',
    '-platform:anycpu', '-warn:4', '-nowarn:1701,1702',
    "-out:$dist\GW2Monitor.exe",
    "-win32icon:$obj\app.ico",
    "-win32manifest:$root\src\app.manifest",
    "-resource:$root\src\MainWindow.xaml,GW2Monitor.MainWindow.xaml"
) + ($refs | ForEach-Object { "-r:$_" }) + (Get-ChildItem "$root\src\*.cs" | ForEach-Object { $_.FullName })

& $csc @cscArgs
if ($LASTEXITCODE -ne 0) { throw "Build failed" }

$size = [math]::Round((Get-Item "$dist\GW2Monitor.exe").Length / 1KB)
Write-Host "OK  ->  $dist\GW2Monitor.exe  ($size KB)" -ForegroundColor Green
