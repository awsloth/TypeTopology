Anna Williams 14 February 2026

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.DependentEquality
open import UF.Equiv renaming (inverse to e-inverse) hiding (_≅_)
open import UF.Sets-Properties
open import UF.DependentEquality
open import Notation.UnderlyingType
open import Categories.Wild
open import Categories.Pre
open import Categories.Univalent
open import Categories.Notation.Pre
open import Categories.Notation.Univalent
open import Categories.Displayed.Pre
open import Categories.Displayed.Univalent
open import Categories.Displayed.Notation.Pre
open import Categories.Displayed.Notation.Univalent

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
TotalPrecategory {𝓤} {𝓥} {𝓦} {𝓨} {P} D = (total-wild-category
                                          , total-is-precategory)
 where
  open PrecategoryNotation P
  open DisplayedPrecategoryNotation D

  total-wild-category : WildCategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
  total-wild-category = wildcategory
                       (Σ p ꞉ obj P , obj[ p ])
                       (λ (a , x) (b , y) → Σ f ꞉ hom a b , hom[ f ] x y)
                       (𝒊𝒅 , D-𝒊𝒅)
                       (λ (g , 𝕘) (f , 𝕗) → g ◦ f , 𝕘 ○ 𝕗)
                       (λ (f , 𝕗) → to-Σ-＝ (𝒊𝒅-is-left-neutral f
                                            , Idtofun (dep-id _ _)
                                               (D-𝒊𝒅-is-left-neutral 𝕗)))
                       (λ (f , 𝕗) → to-Σ-＝ (𝒊𝒅-is-right-neutral f
                                            , Idtofun (dep-id _ _)
                                               (D-𝒊𝒅-is-right-neutral 𝕗)))
                       (λ f g h → to-Σ-＝ (assoc _ _ _
                                          , Idtofun (dep-id _ _) D-assoc))
   where
    dep-id = dependent-Id-via-transport

  total-is-precategory : is-precategory total-wild-category
  total-is-precategory _ _ = Σ-is-set (hom-is-set P) (λ _ → hom[-]-is-set)

TotalCategory : {𝓦 𝓨 : Universe}
                {C : Category 𝓤 𝓥}
                (D : DisplayedCategory 𝓦 𝓨 ⟨ C ⟩)
              → Category (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
TotalCategory {_} {_} {_} {_} {C} D = TotalPrecategory ⟨ D ⟩ , total-is-category
 where
  open CategoryNotation C
  open PrecategoryNotation (TotalPrecategory ⟨ D ⟩)
  open DisplayedCategoryNotation D

  total-is-category : is-category (TotalPrecategory ⟨ D ⟩)
  total-is-category (a , x) (b , y) = (forwards , has-section) , (forwards , is-section)
   where
    forwards : (a , x) ≅ (b , y) → (a , x) ＝ (b , y)
    forwards ((f , 𝕗) , (f⁻¹ , 𝕗⁻¹) , l , r) = to-Σ-＝ (h , other-part)
     where
      lp1 = ap pr₁ l
      rp1 = ap pr₁ r

      pr1-bit : a ≅ b
      pr1-bit = (f , f⁻¹ , lp1 , rp1)

      h : a ＝ b
      h = (e-inverse _ (id-to-iso-is-equiv C a b) pr1-bit)

      test : x ≅[ id-to-iso a b h ] y
           → x ＝⟦ obj[_] , h ⟧ y
      test = e-inverse _ (D-id-to-iso-is-equiv D h x y)

      other-part : transport obj[_] h x ＝ y
      other-part = Idtofun (dependent-Id-via-transport _ _) (test {!!})

    has-section : (e : (a , x) ≅ (b , y)) → id-to-iso (a , x) (b , y) (forwards e) ＝ e
    has-section e = {!!}

    is-section : (e : a , x ＝ b , y) → forwards (id-to-iso (a , x) (b , y) e) ＝ e
    is-section refl = {!!}
     
\end{code}
