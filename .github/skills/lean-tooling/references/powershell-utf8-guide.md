# PowerShell での UTF-8 安全な出力キャプチャ

> **`repl.ps1` 経由では対処不要**: バッチ・Persistent 両モードで `StandardInputEncoding` と
> `[Console]::OutputEncoding` が UTF-8 に自動設定される。`ℕ`・`⊢`・`≤` 等はそのまま使える。
>
> このガイドは `lake exe repl` を**スクリプト外から直接呼び出す場合**や、
> `lake env lean` 等の他コマンドの出力をキャプチャする場合に参照する。

Lean の出力には Unicode 文字（`↓reduceIte`、`⊢`、`≤` 等）が含まれる。
PowerShell のパイプ (`|`) や `Set-Content` は文字化けを起こすため、以下のパターンを使用する。

## NG パターン（文字化けする）

```powershell
# ❌ パイプ経由 → Unicode 文字が壊れる
lake env lean --json file.lean | Set-Content output.jsonl -Encoding UTF8

# ❌ Out-File → BOM 付き UTF-8 になる
lake env lean --json file.lean | Out-File output.jsonl -Encoding utf8
```

## OK パターン（.NET ProcessStartInfo）

```powershell
# ✅ .NET の Process を使って直接 UTF-8 で読む
$psi = New-Object System.Diagnostics.ProcessStartInfo
$psi.FileName = "lake"
$psi.Arguments = "env lean --json file.lean"
$psi.RedirectStandardOutput = $true
$psi.RedirectStandardError = $true
$psi.UseShellExecute = $false
$psi.StandardOutputEncoding = [System.Text.Encoding]::UTF8
$p = [System.Diagnostics.Process]::Start($psi)
$stdout = $p.StandardOutput.ReadToEnd()
$p.WaitForExit()

# BOM なし UTF-8 で書き出し
[System.IO.File]::WriteAllText("output.jsonl", $stdout,
    (New-Object System.Text.UTF8Encoding $false))
```

## ファイル読み書きの安全なパターン

```powershell
# 読み取り
$content = [System.IO.File]::ReadAllText($path, [System.Text.Encoding]::UTF8)

# 書き込み（BOM なし UTF-8）
[System.IO.File]::WriteAllText($path, $content,
    (New-Object System.Text.UTF8Encoding $false))
```

**原則**: Lean の出力を扱うスクリプトでは、常に `.NET` の I/O API を使い、
PowerShell のパイプ・リダイレクトは避ける。
