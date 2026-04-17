# PowerShell 文字列置換の規則

**PowerShell による一括文字列置換は常に `-creplace`（case-sensitive）を使用すること。**
`-replace`（case-insensitive）はプロジェクト内では使用禁止。

```powershell
# ✅ 正しい置換（case-sensitive）
$content = $content -creplace 'sortFU', 'sortFallingUnits'

# ❌ 禁止（case-insensitive のため fU も FU も置換してしまう）
$content = $content -replace 'fU', 'floatingUnits'
```

> **理由**: 同一単語で大小文字が異なる意味を持つ場合（例: `fU`（関数省略形）と `FU`（プロース略称））に、誤置換が発生し再置換が必要になる。
