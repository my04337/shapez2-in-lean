# S2IL — ソースコード構成

## 3分類

| カテゴリ | フォルダ | 概要 |
|---------|---------|------|
| **シェイプ本体** | `Shape/` | シェイプの型定義とシェイプコード表現 |
| **シェイプの振る舞い** | `Behavior/` | 落下・砕け散り・回転・切断・積層・着色・混色・結晶化などの操作 |
| **加工装置** | `Machine/` | 各装置の `Option` ラッパー（有効入力がある場合のみ出力） |

## Shape/ — シェイプ本体の定義

| ファイル | 内容 |
|---------|------|
| `Color.lean` | カラー型（8色）・文字変換・混色関数・代数的性質 |
| `PartCode.lean` | パーツコード型（6種）・RegularPartCode（4種） |
| `Quarter.lean` | 象限型（empty / pin / crystal / colored） |
| `Layer.lean` | レイヤ構造体（4象限の組） |
| `Shape.lean` | シェイプ構造体・シリアライズ・正規化 |
| `QuarterPos.lean` | 方角・レイヤインデックス・象限位置 |
| `GameConfig.lean` | ゲーム設定（構造体）・プリセット（vanilla4 / vanilla5）・truncate |

## Behavior/ — シェイプの振る舞い

| ファイル | 内容 |
|---------|------|
| `Rotate.lean` | 回転（CW / CCW / 180°）・合成・逆元定理 |
| `CrystalBond.lean` | 結晶結合判定・クラスタ列挙 |
| `Shatter.lean` | 砕け散り（切断時 / 落下時 / truncate 時） |
| `Gravity.lean` | 構造結合・接地判定・落下単位・落下処理 |
| `Stacker.lean` | 積み重ね（配置 → 砕け散り → 落下 → truncate） |
| `PinPusher.lean` | ピン押し（持ち上げ → ピン生成 → 砕け散り → 落下） |
| `CrystalGenerator.lean` | 結晶化（隙間・ピンへの結晶充填）・冪等性 |
| `Painter.lean` | 着色（最上位レイヤ）・冪等性 |
| `Cutter.lean` | 切断（Half-Destroyer / Cutter / Swapper） |
| `ColorMixer.lean` | 混色（Color.mix のラッパー） |

## Machine/ — 加工装置

| ファイル | 内容 |
|---------|------|
| `Machine.lean` | 全装置の `Option` 入力対応ラッパー関数 |