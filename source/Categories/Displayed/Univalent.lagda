Anna Williams 14 February 2026

Definition of univalent displayed category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import Notation.UnderlyingType
open import Categories.Pre
open import Categories.Notation.Pre
open import Categories.Notation.Univalent
open import Categories.Displayed.Pre
open import Categories.Displayed.Notation.Pre

module Categories.Displayed.Univalent where

\end{code}

We define the property of being a displayed category akin to that of being a
category.

\begin{code}

module _ {P : Precategory 𝓤 𝓥} (D : DisplayedPrecategory 𝓦 𝓣 P) where
 open DispPrecatNotation D

 is-displayed-category : (𝓤 ⊔ 𝓦 ⊔ 𝓣) ̇
 is-displayed-category = (c c' : obj P)
                    (e : c ＝ c')
                    (d : obj[ c ])
                    (d' : obj[ c' ])
                  → is-equiv (D-id-to-iso e d d')


 is-displayed-category-is-prop : (fe : Fun-Ext)
                               → is-prop (is-displayed-category)
 is-displayed-category-is-prop fe x y = Π₅-is-prop fe I _ _
  where
   I : (c c' : obj P)
       (e : c ＝ c')
       (d : obj[ c ])
       (d' : obj[ c' ])
     → is-prop (is-equiv (D-id-to-iso e d d'))
   I c c' e d d' = being-equiv-is-prop (λ 𝓤 𝓥 → fe {𝓤} {𝓥})
                                       (D-id-to-iso e d d')

\end{code}


We can now define displayed categories. These are exactly precategories such
that the map, D-id-to-iso is an eqivalence.

\begin{code}

DisplayedCategory : (𝓤 𝓥 : Universe)
                    {𝓦 𝓣 : Universe}
                    (P : Precategory 𝓦 𝓣)
                  → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ⁺ ̇
DisplayedCategory 𝓤 𝓥 P = Σ D ꞉ DisplayedPrecategory 𝓤 𝓥 P
                          , is-displayed-category D
\end{code}

Projections from a displayed category.

\begin{code}

instance
  underlying-disp-precat-of-disp-cat
   : {P : Precategory 𝓦 𝓣}
   → Underlying-Type (DisplayedCategory 𝓤 𝓥 P) (DisplayedPrecategory 𝓤 𝓥 P)
  ⟨_⟩ {{underlying-disp-precat-of-disp-cat}} (D , _) = D


D-id-to-iso-is-equiv : {P : Precategory 𝓦 𝓣}
                       (D : DisplayedCategory 𝓤 𝓥 P)
                     → is-displayed-category ⟨ D ⟩
D-id-to-iso-is-equiv = pr₂

\end{code}
