Anna Williams, 29 October 2025

Examples involving displayed categories

\begin{code}


{-# OPTIONS --safe --without-K #-}

open import Groups.Type
open import MLTT.Spartan
open import UF.Equiv hiding (_≅_ ; _≅⟨_⟩_)
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import UF.Univalence

module Categories.DisplayedCategories.DisplayedExamples (fe : Fun-Ext) (uv : Univalence) where

open import Categories.Type fe renaming (make to wildmake)
open import Categories.DisplayedCategories.Type fe

\end{code}

Defining set

\begin{code}

SetPrecat : {𝓤 : Universe} → Precategory (𝓤 ⁺) 𝓤
SetPrecat {𝓤} = (set-wild , set-is-precat)
 where
  set-wild : WildCategory (𝓤 ⁺) 𝓤
  set-wild = wildmake (Σ S ꞉ 𝓤 ̇ , is-set S)
                      (λ (X , _) (Y , _) → X → Y)
                      (λ x → x)
                      (λ g f x → g (f x))
                      (λ _ → refl)
                      (λ _ → refl)
                      refl

  set-is-precat : is-precategory set-wild
  set-is-precat (X , sX) (Y , sY) = Π-is-set fe λ _ → sY

  iso-to-id : (a b : obj set-wild) → a ≅⟨ set-wild ⟩ b → a ＝ b
  iso-to-id (X , sX) (Y , sY) (g , f , l-id , r-id) = to-subtype-＝ (λ _ → being-set-is-prop fe) ((pr₁ (pr₁ ((uv 𝓤) X Y)))
                                                                                             (g , (f , forwards) , (f , backwards)))
   where
    forwards : (λ x → g (f x)) ∼ (λ x → x)
    forwards y = g (f y)           ＝⟨ refl ⟩
                 (λ x → g (f x)) y ＝⟨ ap (λ f → f y) r-id ⟩
                 (λ x → x) y       ＝⟨ refl ⟩
                 y ∎

    backwards : (λ x → f (g x)) ∼ (λ x → x)
    backwards x = f (g x) ＝⟨ refl ⟩
                  (λ y → f (g y)) x ＝⟨ ap (λ f → f x) l-id ⟩
                  (λ y → y) x ＝⟨ refl ⟩
                  x ∎

DispGrp : {𝓤 : Universe} → DisplayedPrecategory 𝓤 𝓤 (SetPrecat {𝓤})
DispGrp = record
           { obj-fam = λ (X , sX) → Group-structure X
           ; hom-fam = λ f x y → is-hom (_ , x) (_ , y) f
           ; hom-fam-is-set = λ {_} {_} {f} {x} {y} → props-are-sets (being-hom-is-prop fe (_ , x) (_ , y) f) 
           ; id-fam = λ x → id-is-hom (_ , x)
           ; comp = λ {a} {b} {c} {g} {f} {x} {y} {z} gyz fxy → ∘-is-hom (_ , x) (_ , y) (_ , z) f g fxy gyz
           ; cmp-right-id = {!!}
           ; cmp-left-id = {!!}
           ; cmp-assoc = {!!}
           }

\end{code}
