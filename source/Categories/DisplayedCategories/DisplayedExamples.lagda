Anna Williams, 29 October 2025

Examples involving displayed categories

\begin{code}


{-# OPTIONS --safe --without-K #-}

open import Groups.Type renaming (assoc to g-assoc)
open import MLTT.Spartan hiding (id)
open import UF.Base
open import UF.DependentEquality
open import UF.Equiv hiding (_≅_ ; _≅⟨_⟩_)
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import UF.Univalence

module Categories.DisplayedCategories.DisplayedExamples where

open import Categories.Type
open import Categories.DisplayedCategories.Type

\end{code}

Defining set

\begin{code}

to-wildcat-＝ : (W W' : WildCategory 𝓤 𝓥)
              → (obj-eq : obj W ＝ obj W')
              → (hom-eq : hom {{W}} ＝⟦ (λ v → v → v → _ ̇ ) , obj-eq ⟧  hom {{W'}})
              → (id-eq : {!!})
              → (comp-eq : {!!})
              → W ＝ W'
to-wildcat-＝ W W' refl refl refl refl = {!!}

module _ (fe : Fun-Ext) where
 SetWildcat : {𝓤 : Universe} → WildCategory (𝓤 ⁺) 𝓤
 SetWildcat {𝓤} = wildcat-make (Σ S ꞉ 𝓤 ̇ , is-set S)
                       (λ (X , _) (Y , _) → X → Y)
                       (λ x → x)
                       (λ g f x → g (f x))
                       (λ _ → refl)
                       (λ _ → refl)
                       refl

 SetPrecat : {𝓤 : Universe} → Precategory (𝓤 ⁺) 𝓤
 SetPrecat = (SetWildcat , set-is-precat)
  where
   set-is-precat : is-precategory SetWildcat
   set-is-precat (X , sX) (Y , sY) = Π-is-set fe λ _ → sY

 DispGrp : {𝓤 : Universe} → DisplayedPrecategory 𝓤 𝓤 (SetPrecat {𝓤})
 DispGrp {𝓤} = record
            { obj-fam = λ (X , sX) → Group-structure X
            ; hom-fam = λ f x y → is-hom (_ , x) (_ , y) f
            ; hom-fam-is-set = λ {_} {_} {f} {x} {y} → props-are-sets (being-hom-is-prop fe (_ , x) (_ , y) f) 
            ; id-fam = λ x → id-is-hom (_ , x)
            ; comp = λ {a} {b} {c} {g} {f} {x} {y} {z} gyz fxy → ∘-is-hom (_ , x) (_ , y) (_ , z) f g fxy gyz
            ; cmp-right-id = {!!}
            ; cmp-left-id = {!!}
            ; cmp-assoc = {!!}
            }

 GroupPrecat : {𝓤 : Universe} → Precategory (𝓤 ⁺) 𝓤
 GroupPrecat {𝓤} = wildcat-make (Σ X ꞉ 𝓤 ̇ , Group-structure X)
                                (λ G H → Σ f ꞉ (⟨ G ⟩ → ⟨ H ⟩) , is-hom G H f )
                                (λ {G} → (λ x → x) , id-is-hom G)
                                (λ {F} {G} {H} (g , hg) (f , hf) → (λ x → g (f x)) , ∘-is-hom F G H f g hf hg )
                                (λ f → to-Σ-＝ (refl , {!!}))
                                {!!}
                                {!!}
                              , {!!}

 disp-eq-precat : {𝓤 : Universe} → GroupPrecat {𝓤} ＝ TotalPrecategory (DispGrp {𝓤})
 disp-eq-precat = to-Σ-＝ {!!}

\end{code}
