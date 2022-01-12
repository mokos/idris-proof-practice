# Idris で定理証明をやっていく
## 最終目標
直観主義論理（排中律を使わない）で素数の無限性を証明する

# 方針
## できるだけPreludeの機能を使わず自分で定義していく

## Natを使わない
``` idris
data N = O | S N
```

見やすさを重視してZではなくOをゼロとした。

``` idris
prefix 11 `S`
```

とすると、S (S n)をSの演算子の優先順位が強くなってS S nと書けて地味にうれしい。
(11は99とかでもいい。Haskellでは演算子の優先度は9が最大のようだが、Idrisでは違うみたい)

## 論理和にEitherを使わない 

Either は Left と Right の文字数が揃わないし文字数が多いので
``` idris
data (||) a b = L a | R b
```
と定義して使う。

数学記号と近づけたければ、入力がしづらいが
``` idris
a \/ b
```
としてもいいかもしれない。

## 識別子には日本語を積極的に使って分かりやすくする 
定理証明プログラミングはそもそも難しい。

用語を無理に英語にするとハードルが上がるのでかっこつけない。

# ここまでやった
## 古典論理と直観主義論理の理解
排中律と同値ないくつかの命題

ドモルガン論理という、古典論理と直観主義論理の中間にある論理の存在も知った。

## reverseのreverseは元通り
素数とは特に関係ないが練習でやってみた。

## 自然数
和と積の交換則、結合則、分配則などの証明
不等号の法則いろいろの証明
割り切ること、素数の定義、いくつかの性質の証明

## 整数
和と積を定義し、交換則、結合則、分配則などの証明
