Anna Williams 14 February 2026

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Notation.UnderlyingType
open import UF.Base
open import UF.Sets-Properties
open import UF.DependentEquality
open import Categories.Wild
open import Categories.Pre
open import Categories.Univalent
open import Categories.Notation.Pre
open import Categories.Displayed.Pre
open import Categories.Displayed.Univalent
open import Categories.Displayed.Notation.Pre

module Categories.Displayed.Total where

\end{code}

We can now define a total precategory. This is the category that pairs up the
objects of a 'base' precategory with the corresponding objects index by that
object in the displayed precategory. That is, the objects are of the form
Σ x : obj P , obj[ x ]. We similarly define the homomorphisms and other fields.

\begin{code}

TotalPrecategory : {𝓦 𝓨 : Universe}
                   {P : Precategory 𝓤 𝓥}
                   (D : DisplayedPrecategory 𝓦 𝓨 P)
                 → Precategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
TotalPrecategory {𝓤} {𝓥} {𝓦} {𝓨} {P} D = (totalwildcategory
                                          , total-is-precategory)
 where
  open PrecategoryNotation P
  open DispPrecatNotation D

  totalwildcategory : WildCategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
  totalwildcategory = wildcategory
                       (Σ c ꞉ obj P , obj[ c ])
                       (λ (a , x) (b , y) → Σ f ꞉ hom a b , hom[ f ] x y)
                       (𝒊𝒅 , D-𝒊𝒅)
                       (λ (g' , g) (f' , f) → g' ○ f' , g ◦ f)
                       (λ (f' , f) → to-Σ-＝ (𝒊𝒅-is-left-neutral f'
                                   , Idtofun (did _ _)
                                     (D-𝒊𝒅-is-left-neutral f)))
                       (λ (f' , f) → to-Σ-＝ (𝒊𝒅-is-right-neutral f'
                                   , Idtofun (did _ _)
                                     (D-𝒊𝒅-is-right-neutral f)))
                       (λ f g h → to-Σ-＝ (assoc _ _ _
                                , Idtofun (did _ _) D-assoc))
   where
    did = dependent-Id-via-transport

  total-is-precategory : is-precategory totalwildcategory
  total-is-precategory _ _ = Σ-is-set (hom-is-set P) (λ _ → hom[-]-is-set)

\end{code}

Total category

\begin{code}

TotalCategory : (C : Category 𝓤 𝓥) (D : DisplayedCategory 𝓦 𝓣 ⟨ C ⟩) → Category (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣)
TotalCategory C D = TotalPrecategory ⟨ D ⟩ , total-is-category
 where
  total-is-category : is-category (TotalPrecategory ⟨ D ⟩)
  total-is-category a b = {!id-to-iso-is-equiv C!}

\end{code}

