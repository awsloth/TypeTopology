Anna Williams 14 February 2026

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import Notation.UnderlyingType
open import Categories.Pre
open import Categories.Notation.Pre
open import Categories.Notation.Univalent
open import Categories.Displayed.Pre
open import Categories.Displayed.Notation.Pre

module Categories.Displayed.Univalent where

\end{code}

\begin{code}

module _ {P : Precategory 𝓤 𝓥} (D : DisplayedPrecategory 𝓦 𝓣 P) where
 open DispPrecatNotation D

 is-disp-category : (𝓤 ⊔ 𝓦 ⊔ 𝓣) ̇
 is-disp-category = {c c' : obj P}
                    (e : c ＝ c')
                    (d : obj[ c ])
                    (d' : obj[ c' ])
                  → is-equiv (id-to-iso-disp e d d')

\end{code}


We now look at displayed categories. These are exactly precategories
such that following map, id-to-iso-disp is an eqivalence.

\begin{code}

DisplayedCategory : (𝓤 𝓥 : Universe)
                    {𝓦 𝓣 : Universe}
                    (P : Precategory 𝓦 𝓣)
                  → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ⁺ ̇
DisplayedCategory 𝓤 𝓥 P = Σ D ꞉ DisplayedPrecategory 𝓤 𝓥 P , is-disp-category D
\end{code}

Projections

\begin{code}

instance
  underlying-disp-precat-of-disp-cat
   : {P : Precategory 𝓦 𝓣} → Underlying-Type (DisplayedCategory 𝓤 𝓥 P) (DisplayedPrecategory 𝓤 𝓥 P)
  ⟨_⟩ {{underlying-disp-precat-of-disp-cat}} (D , _) = D

\end{code}
