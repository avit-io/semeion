{-# OPTIONS --safe --without-K #-}

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  semeion — σημεῖον, il segno.                                          ║
-- ║                                                                        ║
-- ║  Tesi: dare ai segnali osservabili una GEOMETRIA intrinseca tale che   ║
-- ║  la visualizzazione fedele EMERGA come teorema, portando il legame     ║
-- ║  dato↔widget dal regime della stipulazione pura (gusto) a quello       ║
-- ║  dell'emergenza (prova).                                               ║
-- ║                                                                        ║
-- ║  Tre stadi:  Signal ──teorema──▶ Display ──adapter──▶ PanelKind.       ║
-- ║  semeion si ferma a `Display` (la primitiva GEOMETRICA): non importa   ║
-- ║  Penelope, dipende solo da prometea. Il nome Grafana del pannello è    ║
-- ║  l'epifenomeno di un epifenomeno.                                      ║
-- ║                                                                        ║
-- ║  Disciplina (--without-K): l'emergenza è il default. La stipulazione   ║
-- ║  è ammessa SOLO dove la struttura non determina — quarantenata e       ║
-- ║  marcata, come si invoca K localmente in una singola prova, mai come   ║
-- ║  assioma globale.                                                      ║
-- ╚══════════════════════════════════════════════════════════════════════╝

module Semeion.Signal where

open import Data.Nat     as ℕ using (ℕ; suc; z≤n; s≤s)
open import Data.Fin     using (Fin)
open import Data.List    using (List; _∷_; [])
open import Data.Product using (∃-syntax; _,_)
open import Data.Integer as ℤ using (ℤ; +_)
import      Data.Integer.Properties as ℤ
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_; _≤_; toℚᵘ)
import      Data.Rational.Properties as ℚ
open import Data.Rational.Unnormalised as ℚᵘ using (mkℚᵘ)
import      Data.Rational.Unnormalised.Properties as ℚᵘ
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; subst₂)

-- ── Il valore bounded è una PROVA, non una config ──────────────────────
-- Un razionale `v` dentro un intervallo NOTO `[lo,hi]`, con i due testimoni
-- `lo ≤ v` e `v ≤ hi` INCORPORATI. La sua appartenenza all'intervallo non è
-- un campo `min/max` da indovinare: è esibita. Non si può marcare bounded
-- qualcosa senza il testimone. Generalizza il vecchio rapporto good/total
-- ([0,1]) a un fondoscala qualsiasi su ℚ (pool, code, °C, %>1, cap noti).
record Bounded : Set where
  constructor mkBounded
  field
    lo hi v : ℚ
    lo≤v    : lo ≤ v
    v≤hi    : v ≤ hi

-- `Ratio` resta un nome per il caso [0,1] (compat. a valle: Penelope lo cita).
Ratio : Set
Ratio = Bounded

-- ── Il caso [0,1] EMERGE da n ≤ d (regime 1) ───────────────────────────
-- `inUnit n d` con `n ≤ d` (e `d ≠ 0`: zero osservazioni = nessuna lettura,
-- e su ℚ `0/0` non esiste — il vincolo è onesto, non un artificio) dà il
-- valore `n/d` nell'unità [0,1]. I due bound NON si stipulano: si provano
-- al livello non-normalizzato, dove l'ordine È la moltiplicazione incrociata
-- su ℤ, e si trasportano. È il vecchio `m≤m+n` dell'SLI, ora su ℚ.
private
  unit-lo : ∀ (n d : ℕ) → 0ℚ ≤ (+ n) / suc d
  unit-lo n d = ℚ.toℚᵘ-cancel-≤ (ℚᵘ.≤-respʳ-≃ (ℚᵘ.≃-sym bridge) g)
    where
      Q = mkℚᵘ (+ n) d
      bridge : toℚᵘ ((+ n) / suc d) ℚᵘ.≃ Q
      bridge = ℚ.toℚᵘ-fromℚᵘ Q
      g : toℚᵘ 0ℚ ℚᵘ.≤ Q
      g = ℚᵘ.*≤* le
        where le : (+ 0) ℤ.* (+ suc d) ℤ.≤ (+ n) ℤ.* (+ 1)
              le = subst₂ ℤ._≤_ (sym (ℤ.*-zeroˡ (+ suc d)))
                                (sym (ℤ.*-identityʳ (+ n))) (ℤ.+≤+ z≤n)

  unit-hi : ∀ (n d : ℕ) → n ℕ.≤ suc d → ((+ n) / suc d) ≤ 1ℚ
  unit-hi n d n≤sd = ℚ.toℚᵘ-cancel-≤ (ℚᵘ.≤-respˡ-≃ (ℚᵘ.≃-sym bridge) g)
    where
      Q = mkℚᵘ (+ n) d
      bridge : toℚᵘ ((+ n) / suc d) ℚᵘ.≃ Q
      bridge = ℚ.toℚᵘ-fromℚᵘ Q
      g : Q ℚᵘ.≤ toℚᵘ 1ℚ
      g = ℚᵘ.*≤* le
        where le : (+ n) ℤ.* (+ 1) ℤ.≤ (+ 1) ℤ.* (+ suc d)
              le = subst₂ ℤ._≤_ (sym (ℤ.*-identityʳ (+ n)))
                                (sym (ℤ.*-identityˡ (+ suc d))) (ℤ.+≤+ n≤sd)

inUnit : (n d : ℕ) → ⦃ ℕ.NonZero d ⦄ → n ℕ.≤ d → Bounded
inUnit n (suc d) n≤d = mkBounded 0ℚ 1ℚ ((+ n) / suc d) (unit-lo n d) (unit-hi n d n≤d)

-- Esempio: un SLI 1/2 nell'unità [0,1]. I due bound SONO le dimostrazioni
-- 0 ≤ valore ≤ 1. (Una magnitudo unbounded — rate, latenza-ms — non ha nulla
--  da mettere qui: per questo finisce in `flow`, non in `ratio`.)
exampleSLI : Bounded
exampleSLI = inUnit 1 2 (s≤s z≤n)

-- ── Codominio: la struttura intrinseca del valore ──────────────────────
data Codomain : Set where
  flow  : Codomain                 -- magnitudo continua SENZA fondoscala
                                   --   intrinseco: rate, count, latenza-ms
  ratio : Bounded → Codomain       -- continua, bounded [lo,hi], testimoni
                                   --   incorporati: SLI, saturazione, budget
  state : (n : ℕ) → Fin n → Codomain  -- categoriale: n stati, quello corrente

-- ── Indice: scalare singolo o famiglia etichettata ─────────────────────
data Index : Set where
  point      : Index               -- un solo valore
  comparable : Index               -- famiglia su UNA scala condivisa
                                   --   (per-servizio SLI: tutti in [0,1])
  mixed      : Index               -- famiglia su scale eterogenee (unità diverse)

record Signal : Set where          -- NB: nessun campo `intent`. L'intento
  constructor mkSignal             --     è il K locale, non un asse del segnale.
  field
    cod : Codomain
    idx : Index

-- ── Display: la primitiva GEOMETRICA, nominata da cos'È, non da Grafana ─
data Display : Set where
  arc        : Display   -- un valore dentro un intervallo noto (→ gauge)
  bars       : Display   -- N valori comparabili su una scala (→ bargauge)
  number     : Display   -- una magnitudo senza fondoscala (→ stat)
  line       : Display   -- una traiettoria continua nel tempo (→ timeseries)
  stateBands : Display   -- una traiettoria categoriale (→ status-history)
  grid       : Display   -- una famiglia non comparabile (→ table)

-- ── L'onestà è NEL TIPO ────────────────────────────────────────────────
-- Il codominio di `displayAt` testimonia se la scelta è emersa o no.
data Faithful : Set where
  forced          : Display → Faithful         -- emerge: unico fedele
  underdetermined : List Display → Faithful     -- la struttura non forza:
                                                --   menu onesto, serve un fiat

-- ── L'intento: l'UNICA stipulazione (il K locale) ──────────────────────
-- Non vive nel segnale. È la domanda dell'operatore, pagata al sito d'uso.
data Intent : Set where
  now      : Intent   -- "quanto vale adesso"
  overTime : Intent   -- "che traiettoria ha"

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  Il teorema centrale come funzione totale.                            ║
-- ║  Pagato l'intento, la STRUTTURA forza il display — tranne UNA cella.  ║
-- ╚══════════════════════════════════════════════════════════════════════╝
displayAt : Intent → Signal → Faithful
-- overTime: la continuità del codominio forza linea vs bande. Una linea
-- tracciata fra FAIL e OK sarebbe una menzogna geometrica ⇒ stateBands.
displayAt overTime (mkSignal flow        _)          = forced line
displayAt overTime (mkSignal (ratio _)   _)          = forced line
displayAt overTime (mkSignal (state _ _) _)          = forced stateBands
-- now, bounded: l'intervallo intrinseco È l'arco; N comparabili sono barre.
displayAt now (mkSignal (ratio _)   point)      = forced arc
displayAt now (mkSignal (ratio _)   comparable) = forced bars
displayAt now (mkSignal (ratio _)   mixed)      = forced bars   -- i ratio
                                              -- condividono [0,1]: sempre comparabili
-- now, unbounded: niente fondoscala ⇒ numero nudo (un arco avrebbe estremi fiat).
displayAt now (mkSignal flow        point)      = forced number
displayAt now (mkSignal flow        mixed)      = forced grid    -- unità eterogenee
-- L'UNICA cella sottodeterminata: magnitudi unbounded comparabili, adesso.
-- Lista di stat vs tabella è gusto. La struttura NON sceglie ⇒ menu.
displayAt now (mkSignal flow        comparable) = underdetermined (number ∷ grid ∷ [])
-- now, categoriale: stato corrente come badge / tabella di stati.
displayAt now (mkSignal (state _ _) point)      = forced number
displayAt now (mkSignal (state _ _) comparable) = forced grid
displayAt now (mkSignal (state _ _) mixed)      = forced grid

-- Senza pagare l'intento (senza il K), lo spread irriducibile del segnale.
viz : Signal → List Display
viz s = collect (displayAt now s) ++ᵈ collect (displayAt overTime s)
  where
    collect : Faithful → List Display
    collect (forced d)           = d ∷ []
    collect (underdetermined ds) = ds
    _++ᵈ_ : List Display → List Display → List Display
    []       ++ᵈ ys = ys
    (x ∷ xs) ++ᵈ ys = x ∷ (xs ++ᵈ ys)

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  TEOREMI                                                              ║
-- ╚══════════════════════════════════════════════════════════════════════╝

-- ── ratio/SLI: la visualizzazione EMERGE, dato l'intento (regime 1) ────
-- "scalare → gauge" non è più un fiat: bounded + point + now ⇒ arc, provato.
sliNow : ∀ (r : Ratio) → displayAt now (mkSignal (ratio r) point) ≡ forced arc
sliNow _ = refl

sliTrend : ∀ (r : Ratio) → displayAt overTime (mkSignal (ratio r) point) ≡ forced line
sliTrend _ = refl

-- Famiglia di SLI per-servizio (tutti in [0,1], comparabili) ⇒ barre.
sliFamily : ∀ (r : Ratio) → displayAt now (mkSignal (ratio r) comparable) ≡ forced bars
sliFamily _ = refl

-- ── Rifiuto onesto: una magnitudo unbounded NON è una gauge ────────────
-- Latenza p99 / rate / count: niente fondoscala. semeion RIFIUTA l'arco
-- (in Grafana è il peccato del fondoscala inventato).
latencyIsNumber : displayAt now (mkSignal flow point) ≡ forced number
latencyIsNumber = refl

latencyNotArc : displayAt now (mkSignal flow point) ≢ forced arc
latencyNotArc ()

-- ── Pagare overTime forza SEMPRE: nessun residuo su quel ramo ──────────
overTimeAlwaysForced : ∀ (s : Signal) → ∃[ d ] displayAt overTime s ≡ forced d
overTimeAlwaysForced (mkSignal flow        _) = line       , refl
overTimeAlwaysForced (mkSignal (ratio _)   _) = line       , refl
overTimeAlwaysForced (mkSignal (state _ _) _) = stateBands , refl

-- ── L'UNICA cella sottodeterminata, esibita (onestà nel tipo) ──────────
-- Non la mascheriamo con una scelta: il tipo dice `underdetermined`.
flowFamilyUnderdetermined :
  displayAt now (mkSignal flow comparable) ≡ underdetermined (number ∷ grid ∷ [])
flowFamilyUnderdetermined = refl
