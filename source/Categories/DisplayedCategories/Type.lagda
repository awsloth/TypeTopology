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

record DisplayedPrecategory (𝓦 𝓣 : Universe)
                            (C : Precategory 𝓤 𝓥)
                          : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
 open CategoryNotation ⟨ C ⟩
 field
  obj[_] : (c : obj C) → 𝓦 ̇
  hom[_] : {a b : obj C}
           (f : hom a b)
           (x : obj[ a ])
           (y : obj[ b ])
         → 𝓣 ̇
  hom[-]-is-set : {a b : obj C}
                  {f : hom a b}
                  {x : obj[ a ]}
                  {y : obj[ b ]}
                → is-set (hom[ f ] x y)
  
  disp-id : {c : obj C}
            {x : obj[ c ]}
          → hom[ id ] x x

  _∘'_ : {a b c : obj ⟨ C ⟩}
         {g : hom b c}
         {f : hom a b}
         {x : obj[ a ]}
         {y : obj[ b ]}
         {z : obj[ c ]}
         (gyz : hom[ g ] y z)
         (fxy : hom[ f ] x y)
       → hom[ g ∘ f ] x z

 private
  hom[-] : {a b : obj C} (x : obj[ a ]) (y : obj[ b ]) → hom a b → 𝓣 ̇
  hom[-] x y = λ - → hom[ - ] x y

 field
  cmp-right-id : {a b : obj ⟨ C ⟩}
                 {f' : hom a b}
                 {x : obj[ a ]}
                 {y : obj[ b ]}
                 (f : hom[ f' ] x y)
               → f ∘' disp-id ＝⟦ hom[-] x y , right-id f' ⟧ f

  cmp-left-id : {a b : obj ⟨ C ⟩}
                {f' : hom a b}
                {x : obj[ a ]}
                {y : obj[ b ]}
                (f : hom[ f' ] x y)
              → disp-id ∘' f ＝⟦ hom[-] x y , left-id f' ⟧ f
  
  cmp-assoc : {a b c d : obj ⟨ C ⟩}
              {f' : hom a b}
              {g' : hom b c}
              {h' : hom c d}
              {x : obj[ a ]}
              {y : obj[ b ]}
              {z : obj[ c ]}
              {w : obj[ d ]}
              {f : hom[ f' ] x y}
              {g : hom[ g' ] y z}
              {h : hom[ h' ] z w}
            → h ∘' (g ∘' f) ＝⟦ hom[-] x w , assoc f' g' h' ⟧ (h ∘' g) ∘' f

\end{code}

Displayed Isomorphism

\begin{code}

 d-is-iso : {c c' : obj C}
            {d : obj[ c ]}
            {d' : obj[ c' ]}
            (isom : c ≅ c')
            (f : hom[ iso isom ] d d')
          → 𝓣 ̇
 d-is-iso {c} {c'} {d} {d'} isom f = Σ g ꞉ hom[ inv (isomorphism-proof isom) ] d' d
                                        , ((g ∘' f ＝⟦ hom[-] d d , l-inv (isomorphism-proof isom) ⟧ disp-id)
                                          × (f ∘' g ＝⟦ hom[-] d' d' , r-inv (isomorphism-proof isom) ⟧ disp-id))

 _≅[_]_ : {c c' : obj ⟨ C ⟩}
          (d : obj[ c ])
          (iso : c ≅ c')
          (d' : obj[ c' ])
        → 𝓣 ̇
 d ≅[ iso ] d' = Σ f ꞉ hom[ pr₁ iso ] d d' , d-is-iso iso f
       
 id-to-iso-disp : {c c' : obj ⟨ C ⟩}
                  (e : c ＝ c')
                  (d : obj[ c ])
                  (d' : obj[ c' ])
                  (e' : d ＝⟦ obj[_] , e ⟧ d')
                → d ≅[ id-to-iso c c' e ] d'
 id-to-iso-disp refl d _ refl = disp-id , disp-id , h , h
  where
   h : disp-id ∘' disp-id ＝⟦ hom[-] d d , left-id id ⟧ disp-id
   h = cmp-left-id disp-id

 is-disp-category : (𝓤 ⊔ 𝓦 ⊔ 𝓣) ̇
 is-disp-category = {c c' : obj C}
                    (e : c ＝ c')
                    (d : obj[ c ])
                    (d' : obj[ c' ])
                  → is-equiv (id-to-iso-disp e d d')

\end{code}

We defined notation for a displayed category

\begin{code}

open DisplayedPrecategory public using (is-disp-category)

record DOBJ {𝓤 𝓥 : Universe}
            {P : Precategory 𝓦 𝓣}
            (D : DisplayedPrecategory 𝓤 𝓥 P)
          : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
 field
  obj[_] : obj P → 𝓤 ̇

open DOBJ {{...}} public

module _ {𝓤 𝓥 : Universe}
         {P : Precategory 𝓦 𝓣}
         (D : DisplayedPrecategory 𝓤 𝓥 P) where
 open CategoryNotation ⟨ P ⟩

 instance
  mod1 : DOBJ D
  obj[_] {{mod1}} = DisplayedPrecategory.obj[_] D

 record DHOM  : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   hom[_] : {a b : obj ⟨ P ⟩} → hom a b → obj[ a ] → obj[ b ] → 𝓥 ̇

 open DHOM {{...}} public

 instance
  mod2 : DHOM
  hom[_] {{mod2}} = DisplayedPrecategory.hom[_] D

 record DCOMP : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   _∘'_ : {a b c : obj P}
          {g : hom b c}
          {f : hom a b}
          {x : obj[ a ]}
          {y : obj[ b ]}
          {z : obj[ c ]}
          (gyz : hom[ g ] y z)
          (fxy : hom[ f ] x y)
       → hom[ g ∘ f ] x z

 open DCOMP {{...}} public

 record DID : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   disp-id : {c : obj P}
             {x : obj[ c ]}
           → hom[ id ] x x

 open DID {{...}} public

 instance
  mod3 : DCOMP
  _∘'_ {{mod3}} = DisplayedPrecategory._∘'_ D


 instance
  mod4 : DID
  disp-id {{mod4}} = DisplayedPrecategory.disp-id D

 record DNotation : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   hom[-]-is-set : {a b : obj P}
                   {f : hom a b}
                   {x : obj[ a ]}
                   {y : obj[ b ]}
                 → is-set (hom[ f ] x y)
   cmp-right-id : {a b : obj P}
                  {f' : hom a b}
                  {x : obj[ a ]}
                  {y : obj[ b ]}
                  (f : hom[ f' ] x y)
                → f ∘' disp-id ＝⟦ (λ - → hom[ - ] x y) , right-id f' ⟧ f

   cmp-left-id : {a b : obj P}
                 {f' : hom a b}
                 {x : obj[ a ]}
                 {y : obj[ b ]}
                 (f : hom[ f' ] x y)
               → disp-id ∘' f ＝⟦ (λ - → hom[ - ] x y) , left-id f' ⟧ f
  
   cmp-assoc : {a b c d : obj P}
               {f' : hom a b}
               {g' : hom b c}
               {h' : hom c d}
               {x : obj[ a ]}
               {y : obj[ b ]}
               {z : obj[ c ]}
               {w : obj[ d ]}
               {f : hom[ f' ] x y}
               {g : hom[ g' ] y z}
               {h : hom[ h' ] z w}
             → h ∘' (g ∘' f)
             ＝⟦ (λ - → hom[ - ] x w) , assoc f' g' h' ⟧
               (h ∘' g) ∘' f

\end{code}


\begin{code}
 
 open DNotation {{...}} public


module DisplayedNotation {𝓤 𝓥 : Universe}
                         {P : Precategory 𝓦 𝓣}
                         (D : DisplayedPrecategory 𝓤 𝓥 P) where
 instance
  tets : DOBJ D
  obj[_] {{tets}} = DisplayedPrecategory.obj[_] D
  

 instance
  tets' : DHOM D
  hom[_] {{tets'}} = DisplayedPrecategory.hom[_] D

 instance
  tets'' : DID D
  disp-id {{tets''}} = DisplayedPrecategory.disp-id D

 instance
  tets''' : DCOMP D
  _∘'_ {{tets'''}} = DisplayedPrecategory._∘'_ D


 instance
  tets''''' : DNotation D
  hom[-]-is-set {{tets'''''}} = DisplayedPrecategory.hom[-]-is-set D
  cmp-right-id {{tets'''''}} = DisplayedPrecategory.cmp-right-id D
  cmp-left-id {{tets'''''}} = DisplayedPrecategory.cmp-left-id D
  cmp-assoc {{tets'''''}} = DisplayedPrecategory.cmp-assoc D

\end{code}

We can now define a total precategory.

\begin{code}

TotalPrecategory : {𝓦 𝓨 : Universe}
                   {C : Precategory 𝓤 𝓥}
                   (D : DisplayedPrecategory 𝓦 𝓨 C)
                 → Precategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
TotalPrecategory {𝓤} {𝓥} {𝓦} {𝓨} {C} D = (wildcategory , total-is-precategory)
 where
  open CategoryNotation ⟨ C ⟩
  open DisplayedNotation D

  wildcategory : WildCategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
  wildcategory = wildcat-make (Σ c ꞉ obj C , obj[ c ])
                              (λ (a , x) (b , y) → Σ f ꞉ hom a b , hom[ f ] x y)
                              (id , disp-id)
                              (λ (g' , g) (f' , f) → (g' ∘ f') , g ∘' f)
                              (λ (f' , f) → to-Σ-＝ (left-id f'
                                                    , (Idtofun (dependent-Id-via-transport _ _)) (cmp-left-id f)))
                              ((λ (f' , f) → to-Σ-＝ (right-id f'
                                                     , (Idtofun (dependent-Id-via-transport _ _)) (cmp-right-id f))))
                              (λ f g h → to-Σ-＝ ((assoc _ _ _)
                                                 , (Idtofun (dependent-Id-via-transport _ _) cmp-assoc)))

  total-is-precategory : is-precategory wildcategory
  total-is-precategory _ _ = Σ-is-set (hom-is-set C) (λ _ → hom[-]-is-set)

\end{code}

We now look at displayed categories. These are exactly precategories
such that following map, id-to-iso-disp is an eqivalence.

\begin{code}

DisplayedCategory : (𝓤 𝓥 : Universe) {𝓦 𝓣 : Universe} (P : Precategory 𝓦 𝓣) → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ⁺ ̇
DisplayedCategory 𝓤 𝓥 P = Σ D ꞉ DisplayedPrecategory 𝓤 𝓥 P , is-disp-category D

\end{code}

begin{code}

TotalCategory : {𝓦 𝓨 : Universe}
                {P : Precategory 𝓤 𝓥}
                (D : DisplayedCategory 𝓦 𝓨 P)
              → Category (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
TotalCategory (D , is-disp) = TotalPrecategory D , is-cat
 where
  is-cat : is-category ⟨ TotalPrecategory D ⟩
  is-cat = {!!}
\end{code}
