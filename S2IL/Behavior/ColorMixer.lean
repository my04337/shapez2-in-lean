-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Shape.Color

/-!
# ColorMixer (混色機)

2つの液剤を接続して混合し、新しい色を生成する建物。

## 概要

混色機は2つの液剤入力を受け取り、等体積で混合した結果の色を出力する。
混色のルールは `Color.mix` で定義される加法混色モデルに基づく。

## 混色のルール

- 原色同士の混色は二次色を生成する (例: Red + Green = Yellow)
- 同色同士の混色は元の色を返す (冪等性)
- White は恒等元として振る舞う (White + X = X)
- 二次色と原色の混色は、共通成分に応じて原色を返す
- 混色は可換だが結合的ではない
-/

namespace ColorMixer

/-- 混色機で2つの色を混合する。`Color.mix` のエイリアス。 -/
def mix (c1 c2 : Color) : Color :=
    c1.mix c2

end ColorMixer
