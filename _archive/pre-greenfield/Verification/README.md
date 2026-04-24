# Verification — 計算的検証スクリプト

このディレクトリには `lake build` の通常ビルドに含まれない**計算的検証スクリプト**を保管する。

## 目的

証明に着手する前に定理の真理値を大規模な計算検証で確認し、偽定理への工数浪費を防止する
（`lean-proof-planning` スキルの実践）。

## 実行方法

```powershell
# 4L 全数検証（~193 万 shapes、10〜30 分）
lake env lean --run Verification/Gravity/ProcessRotate180Check4L.lean

# 5L–16L ランダムサンプリング（~1.87 万 shapes、数分）
lake env lean --run Verification/Gravity/ProcessRotate180Random.lean
```

> `lake build` には含まれないため、必要に応じて手動で実行すること。

## ディレクトリ構成

| ディレクトリ | 対象 | 内容 |
|---|---|---|
| `Gravity/` | `Gravity.lean` の `process_rotate180` | 全数検証・ランダムサンプリング |
