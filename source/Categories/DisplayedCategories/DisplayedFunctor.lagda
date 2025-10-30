Anna Williams, 30 October 2025

Definition of a displayed functor.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import Categories.Category
open import Categories.Functor
open import Categories.DisplayedCategories.DisplayedCategory

module Categories.DisplayedCategories.DisplayedFunctor where

record DisplayedFunctor {C : Category 𝓦 𝓣} {C' : Category 𝓦' 𝓣'} (F : Functor (C ₚ) (C' ₚ)) (D : DisplayedCategory 𝓤 𝓥 C) (D' : DisplayedCategory 𝓤' 𝓥' C') : (𝓦 ⊔ 𝓣 ⊔ 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥') ̇  where
 field
  obj-map : {c : obj (C ₚ)} → (obj-fam {{D}}) c → (obj-fam {{D'}}) (Fobj {{F}} c)
  hom-map : {c c' : obj (C ₚ)} {f : hom {{C ₚ}} c c'} {x : obj-fam {{D}} c} {y : obj-fam {{D}} c'}
          → mor-fam {{D}} f x y → mor-fam {{D'}} (Fhom {{F}} f) (obj-map x) (obj-map y)
  id-map-pres : {c : obj (C ₚ)} {a : obj-fam {{D}} c} → hom-map (id-fam {{D}} a) ＝ (transport (λ v → mor-fam {{D'}} v (obj-map a) (obj-map a)) ((id-pres {{F}} c)⁻¹) (id-fam {{D'}} (obj-map a)))
  map-distrib : {a b c : obj (C ₚ)} {x : obj-fam {{D}} a} {y : obj-fam {{D}} b} {z : obj-fam {{D}} c} {f' : hom {{C ₚ}} a b} {g' : hom {{C ₚ}} b c} {f : mor-fam {{D}} f' x y} {g : mor-fam {{D}} g' y z} → hom-map (comp {{D}} g f) ＝ transport (λ v → mor-fam {{D'}} v (obj-map x) (obj-map z)) ((distrib {{F}})⁻¹) (comp {{D'}} (hom-map g) (hom-map f))

\end{code}
