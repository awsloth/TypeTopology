Anna Williams, 28 October 2025

Definition of a displayed category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)
open import Notation.UnderlyingType
open import UF.Base
open import UF.DependentEquality
open import UF.Equiv hiding (_≅_ ; _≅⟨_⟩_)
open import UF.Sets
open import UF.Sets-Properties

module Categories.DisplayedCategories.Type where

open import Categories.Type 

\end{code}

We first define the notion of a displayed category. This is
exactly a category D and a functor F : D → C. Which satisfies
the usual structure of a category.

\begin{code}

record DisplayedPrecategory (𝓦 𝓨 : Universe) (C : Precategory 𝓤 𝓥) : ((𝓦 ⊔ 𝓨) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
 field
  obj[_] : (c : obj ⟨ C ⟩) → 𝓦 ̇
  hom[_] : {a b : obj ⟨ C ⟩}
           (f : hom {{⟨ C ⟩}} a b)
           (x : obj[ a ])
           (y : obj[ b ])
         → 𝓨 ̇
  hom[-]-is-set : {a b : obj ⟨ C ⟩}
                  {f : hom {{⟨ C ⟩ }} a b}
                  {x : obj[ a ]}
                  {y : obj[ b ]}
                → is-set (hom[ f ] x y)
  
  id-fam : {c : obj ⟨ C ⟩}
           (x : obj[ c ])
         → hom[ id {{⟨ C ⟩}} {c}] x x

  comp : {a b c : obj ⟨ C ⟩}
         {g : hom {{⟨ C ⟩}} b c}
         {f : hom {{⟨ C ⟩}} a b}
         {x : obj[ a ]}
         {y : obj[ b ]}
         {z : obj[ c ]}
         (gyz : hom[ g ] y z)
         (fxy : hom[ f ] x y)
       → hom[ g ∘⟨ ⟨ C ⟩ ⟩ f ] x z

  cmp-right-id : {a b : obj ⟨ C ⟩}
                 {f' : hom {{⟨ C ⟩}} a b}
                 {x : obj[ a ]}
                 {y : obj[ b ]}
                 (f : hom[ f' ] x y)
               → comp f (id-fam x) ＝⟦ (λ - → hom[ - ] x y) , right-id {{⟨ C ⟩}} f' ⟧ f

  cmp-left-id : {a b : obj ⟨ C ⟩}
                {f' : hom {{⟨ C ⟩}} a b}
                {x : obj[ a ]}
                {y : obj[ b ]}
                (f : hom[ f' ] x y)
              → comp (id-fam y) f ＝⟦ (λ - → hom[ - ] x y) , left-id {{⟨ C ⟩}} f' ⟧ f
  
  cmp-assoc : {a b c d : obj ⟨ C ⟩}
              {f' : hom {{⟨ C ⟩}} a b}
              {g' : hom {{⟨ C ⟩}} b c}
              {h' : hom {{⟨ C ⟩}} c d}
              {x : obj[ a ]}
              {y : obj[ b ]}
              {z : obj[ c ]}
              {w : obj[ d ]}
              {f : hom[ f' ] x y}
              {g : hom[ g' ] y z}
              {h : hom[ h' ] z w}
            → comp h (comp g f) ＝⟦ (λ - → hom[ - ] x w) , assoc {{⟨ C ⟩}} ⟧ comp (comp h g) f

open DisplayedPrecategory {{...}} public

\end{code}

We can now define a total precategory.

\begin{code}

TotalPrecategory : {𝓦 𝓨 : Universe} {C : Precategory 𝓤 𝓥} (D : DisplayedPrecategory 𝓦 𝓨 C) → Precategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
TotalPrecategory {𝓤} {𝓥} {𝓦} {𝓨} {C} D = (wildcategory , total-is-precategory)
 where
  wildcategory : WildCategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
  wildcategory = wildcat-make (Σ c ꞉ obj ⟨ C ⟩ , obj[_] {{D}} c)
                              (λ (a , x) (b , y) → Σ f ꞉ hom {{⟨ C ⟩}} a b , hom[_] {{D}} f x y)
                              (λ {(a , x)} → id {{⟨ C ⟩}} , id-fam {{D}} x)
                              (λ (g' , g) (f' , f) → (g' ∘⟨ ⟨ C ⟩ ⟩ f') , comp {{D}} g f)
                              (λ (f' , f) → to-Σ-＝ (left-id {{⟨ C ⟩}} f' , (Idtofun (dependent-Id-via-transport _ _)) (cmp-left-id {{D}} f)))
                              ((λ (f' , f) → to-Σ-＝ (right-id {{⟨ C ⟩}} f' , (Idtofun (dependent-Id-via-transport _ _)) (cmp-right-id {{D}} f))))
                              (to-Σ-＝ (assoc {{⟨ C ⟩}} , (Idtofun (dependent-Id-via-transport _ _)) (cmp-assoc {{D}})))

  total-is-precategory : is-precategory wildcategory
  total-is-precategory _ _ = Σ-is-set (hom-is-set {{C}}) (λ _ → hom[-]-is-set {{D}})

\end{code}

Displayed isomorphism.

\begin{code}

module _ {𝓤 𝓥 𝓤' 𝓥' : Universe} where

 d-is-iso : {C : Precategory 𝓤 𝓥}
            {{D : DisplayedPrecategory 𝓤' 𝓥' C}}
            {c c' : obj ⟨ C ⟩}
            {d : obj[ c ]}
            {d' : obj[ c' ]}
            (iso : c ≅⟨ ⟨ C ⟩ ⟩ c')
            (f : hom[ pr₁ iso ] d d')
          → 𝓥' ̇
 d-is-iso {C} {{D}} {c} {c'} {d} {d'} iso f = Σ g ꞉ hom[ inv {{⟨ C ⟩}} (pr₂ iso) ] d' d
                                              , ((comp g f ＝⟦ (λ - → hom[ - ] d d) , l-inverse {{⟨ C ⟩}} (pr₂ iso) ⟧ id-fam d)
                                                × (comp f g ＝⟦ (λ - → hom[ - ] d' d') , r-inverse {{⟨ C ⟩}} (pr₂ iso) ⟧ id-fam d'))

 _≅[_]_ : {C : Precategory 𝓤 𝓥}
          {{D : DisplayedPrecategory 𝓤' 𝓥' C}}
          {c c' : obj ⟨ C ⟩}
          (d : obj[ c ])
          (iso : c ≅⟨ ⟨ C ⟩ ⟩ c')
          (d' : obj[ c' ])
        → 𝓥' ̇
 d ≅[ iso ] d' = Σ f ꞉ hom[ pr₁ iso ] d d' , d-is-iso iso f
       

\end{code}

We now look at displayed categories. These are exactly precategories
such that following map, id-to-iso-disp is an eqivalence.

\begin{code}

 id-to-iso-disp : {C : Precategory 𝓤 𝓥}
                  {{D : DisplayedPrecategory 𝓤' 𝓥' C}}
                  {c c' : obj ⟨ C ⟩}
                  {e : c ＝ c'}
                  {d : obj[ c ]}
                  {d' : obj[ c' ]}
                  (e' : d ＝⟦ obj[_] , e ⟧ d')
                → d ≅[ id-to-iso {{⟨ C ⟩}} c c' e ] d'
 id-to-iso-disp {C} ⦃ D ⦄ {_} {_} {refl} {d} refl = id-fam d , id-fam d , h , h
  where
   h : comp (id-fam d) (id-fam d) ＝⟦ (λ - → hom[ - ] d d) , left-id {{⟨ C ⟩}} (id {{⟨ C ⟩}}) ⟧ id-fam d
   h = cmp-left-id (id-fam d)

 is-disp-category : {C : Precategory 𝓤 𝓥}
                    (D : DisplayedPrecategory 𝓤' 𝓥' C)
                  → {!!}
 is-disp-category {C} D = (c c' : WildCategory.obj (C .pr₁))
                          (e : c ＝ c')
                          (d : DisplayedPrecategory.obj[ D ] c)
                          (d' : DisplayedPrecategory.obj[ D ] c')
                        → is-equiv (id-to-iso-disp {{D}} {c} {c'} {e} {d} {d'})


 DisplayedCategory : {C : Precategory 𝓤 𝓥} → ((𝓤 ⁺) ⊔ (𝓥 ⁺) ⊔ (𝓤' ⁺) ⊔ (𝓥' ⁺)) ̇
 DisplayedCategory {C} = Σ D ꞉ DisplayedPrecategory 𝓤' 𝓥' C , is-disp-category D

\end{code}
