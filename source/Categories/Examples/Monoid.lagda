Anna Williams, 13 November 2025

The Category of Monoid

\begin{code}

{-# OPTIONS --without-K  #-}

open import Categories.Examples.SetBased
open import Categories.Type hiding (id ; _∘_)
open import MLTT.Spartan
open import UF.FunExt
open import UF.Sets
open import UF.Univalence

module Categories.Examples.Monoid where

\end{code}

\begin{code}

module _ {𝓤 : Universe} (fe : Fun-Ext) (ua : is-univalent 𝓤) where

 Monoid : (𝓤 ⁺) ̇
 Monoid = Σ X ꞉ 𝓤 ̇  , (is-set X)
                    × (Σ _·_ ꞉ (X → X → X)
                    , Σ e ꞉ X
                    , Π x ꞉ X
                    , ((e · x) ＝ x)
                    × ((x · e) ＝ x))

 MonoidHom : Monoid → Monoid → 𝓤 ̇
 MonoidHom (X , _ , (_·_ , e , pe))
           (Y , _ , (_*_ , e' , pe'))
           = Σ f ꞉ (X → Y) , (((x y : X) → f (x · y) ＝ (f x) * (f y)) × (f e ＝ e'))

 MonoidWildCat : WildCategory (𝓤 ⁺) 𝓤
 MonoidWildCat = wildcat-make Monoid
                              MonoidHom
                              (id , ((λ x y → refl) , refl))
                              {!!}
                              {!!}
                              {!!}
                              {!!}

 MonoidCategory : Category (𝓤 ⁺) 𝓤
 MonoidCategory = gen-category {_}
                               {_}
                               {_}
                               {λ X → (is-set X)
                                    × (Σ _·_ ꞉ (X → X → X)
                                    , Σ e ꞉ X
                                    , Π x ꞉ X
                                    , ((e · x) ＝ x)
                                    × ((x · e) ＝ x))}
                               {λ (X , _ , (_·_ , e , _)) (_ , _ , (_*_ , e' , _)) f → (((x y : X) → f (x · y) ＝ (f x) * (f y)) × (f e ＝ e'))}
                               (λ {a} → pr₂ (WildCategory.id MonoidWildCat {a}))
                               (λ f g → pr₂ (f ∘⟨ MonoidWildCat ⟩ g))
                               {!!} -- l-id
                               {!!} -- r-id
                               {!!} -- assoc

                               {!!} -- inverses-are-homs
                               {!!} -- hom-property-is-prop
                               (λ (_ , sA , _) → sA)
                               {!!} -- property to id
                               {!!} -- property to id is retract

                               fe
                               ua
