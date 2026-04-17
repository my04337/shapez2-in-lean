# CrystalBond 同レイヤ色チェック修正の記録

作成日: 2026-04-07

---

## 概要

`CrystalBond.isBondedInLayer` の定義に誤りがあり、同レイヤ内の結晶結合で不要な色チェック (`c1 == c2`) を行っていた。ゲーム実機テストにより色不問であることを確認し、修正した。

## 発見の経緯

ゲーム仕様書の記述と実装の差異を調査した際に発覚。REPL テストで `crcgcrcg` (異色結晶4つ) に対する `shatterOnCut` の結果が実装とゲームで乖離することを確認。

## ゲーム実機テスト結果

### 決定的テスト

| テスト | シェイプコード | 操作 | ゲーム結果 | 意味 |
|---|---|---|---|---|
| **A** | `crcgcb--` | カッター半切り | 空（全砕け） | **同レイヤ異色結晶は結合する** |
| **G** | `CrCr----:crcg----:cr------:cr------` | PinPush (vanilla4) | `P-P-----:CrCr----` | 異色結晶連鎖 shatter 確認 |

### 上下レイヤ間の検証（修正不要の確認）

| テスト | シェイプコード | 操作 | ゲーム結果 | 意味 |
|---|---|---|---|---|
| **I** | `CrcrCrCr:CrCrcgCr` | カッター東半分 | `Crcr----:CrCr----` | 上下レイヤ隣接方角は非結合 |
| **J** | `CrcrCrCr:CrCrCrcg` | カッター東半分 | `Crcr----:CrCr----` | 対角も非結合 |
| **L** | `CrcrCrCr:CrcgCrCr` | カッター東半分 | `Crcr----:Crcg----` | 同方角のみ結合 |

### 確定した結合ルール

| 結合タイプ | 条件 | ゲーム検証 |
|---|---|---|
| 同レイヤ内 | 隣接方角 + 結晶（**色不問**） | テスト A で確定 |
| 上下レイヤ間 | 同方角 + 結晶（色不問） | テスト I/J/L で確定（変更なし） |

## 修正内容

| ファイル | 変更 |
|---|---|
| `CrystalBond.lean` | `isBondedInLayer`: `c1 == c2` → `true`、コメント・対称性証明の簡素化 |
| `Test/Behavior/Shatter.lean` | `crcgcrcg`, `crcrcgcg` の期待値を全砕けに修正、テスト A 追加 |
| `Test/Behavior/PinPusher.lean` | テスト G 追加 |
| `Test/Behavior/Cutter.lean` | `crcrcgcg` のテスト期待値を全砕けに修正（2箇所） |
| `docs/shapez2/crystal-shatter.md` | §3.1 から色条件を削除 |

## 影響範囲

- **Shatter / Cutter / PinPusher / Stacker**: `CrystalBond.cluster` 経由で依存するが、API 境界は不変。テスト期待値のみ修正
- **Gravity (`isStructurallyBonded`)**: 独立した結合定義 (`canFormBond` ベース)。**影響なし**
- **等変性証明 (rotate180)**: 定義の簡素化により証明は短くなる方向。新規 sorry なし
