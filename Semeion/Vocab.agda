{-# OPTIONS --safe --without-K #-}

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  Vocabolario SRE — ogni segnale come la sua struttura intrinseca.     ║
-- ║                                                                        ║
-- ║  Per ciascuno: o il codominio EMERGE (regime 1, il bound è un          ║
-- ║  teorema), o è bounded SOLO sotto un'ipotesi falsificabile sul         ║
-- ║  deployment (regime 2, fedeltà), e allora lo si DICE — il regime è un  ║
-- ║  campo, non una nota a margine.                                        ║
-- ║                                                                        ║
-- ║  Esemplari del contrasto:                                              ║
-- ║   • SLI         — ratio good/(good+bad): bound = m≤m+n. REGIME 1.      ║
-- ║   • saturation  — usage/capacity: bounded SOLO se la capacità è un     ║
-- ║                   tetto rigido. L'ipotesi `usage ≤ capacity` è         ║
-- ║                   FORNITA dall'operatore e FALSIFICABILE. REGIME 2.    ║
-- ║                   Senza l'ipotesi: è `flow`, e la gauge è RIFIUTATA.   ║
-- ╚══════════════════════════════════════════════════════════════════════╝

module Semeion.Vocab where

open import Semeion.Signal

open import Data.Nat            using (ℕ; _+_; _≤_)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Maybe          using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- ── Sotto quale regime il codominio è ciò che dichiara ─────────────────
-- (Il regime 3 — gusto — non compare qui: non produce una lettura fedele,
--  ma un `underdetermined` in `displayAt`. Qui stanno solo le letture.)
data Regime : Set where
  emergent : Regime   -- 1: teorema — il bound (o l'assenza di bound) È la struttura
  fidelity : Regime   -- 2: ipotesi falsificabile sul reale, fornita dall'operatore

-- Un osservabile: il segnale + il regime sotto cui il suo codominio regge.
record Observable : Set where
  constructor obs
  field
    signal : Signal
    regime : Regime

-- Comodità: la lettura "adesso" di un osservabile.
nowReading : Observable → Faithful
nowReading o = displayAt now (Observable.signal o)

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  REGIME 1 — il codominio EMERGE (il bound è un teorema)               ║
-- ╚══════════════════════════════════════════════════════════════════════╝

-- SLI: good su (good+bad). `good ≤ good+bad` è `m≤m+n`: 0 ≤ valore ≤ 1 è
-- DIMOSTRATO dalla decomposizione, non assunto. Nessun input empirico.
sli : (good bad : ℕ) → Observable
sli good bad = obs (mkSignal (ratio (mkRatio good (good + bad) (m≤m+n good bad))) point)
                   emergent

-- level / rate / latencyQuantile: magnitudi SENZA fondoscala intrinseco.
-- Nessun bound da esibire ⇒ `flow`. La loro non-boundedness È la struttura.
level : Observable
level = obs (mkSignal flow point) emergent

rate : Observable
rate = obs (mkSignal flow point) emergent

latencyQuantile : Observable           -- p50/p95/p99: bounded sotto da 0,
latencyQuantile = obs (mkSignal flow point) emergent   -- UNBOUNDED sopra

-- burn-rate: (1-SLI)/(1-SLO). Può valere 14×: niente fondoscala. Ha una
-- soglia a 1 (bruci esattamente il budget) ma una soglia NON è un dominio.
-- ⇒ `flow`. La gauge è rifiutata; semmai uno `stat` con soglia colorata.
burnRate : Observable
burnRate = obs (mkSignal flow point) emergent

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  REGIME 2 — bounded SOLO per fedeltà a un fatto del deployment        ║
-- ╚══════════════════════════════════════════════════════════════════════╝

-- saturation = usage / capacity. È in [0,1] SE E SOLO SE la capacità è un
-- tetto rigido e noto. Quell'`usage ≤ capacity` NON emerge dalla struttura
-- (a differenza dell'SLI): è una claim sul mondo, che il sistema può
-- VIOLARE (uso elastico, burst oltre quota). Per questo la passi tu:
--
--   • `just hyp`  — hai la garanzia del tetto rigido ⇒ `ratio`, REGIME 2.
--                   L'arco emerge, ma la sua fedeltà è CONDIZIONATA a `hyp`.
--   • `nothing`   — tetto soft/elastico, nessuna garanzia ⇒ `flow`.
--                   La gauge è RIFIUTATA: un arco avrebbe un fondoscala che
--                   il sistema può sforare. Solo un numero è onesto.
saturation : (usage capacity : ℕ) → Maybe (usage ≤ capacity) → Observable
saturation usage capacity (just hyp) =
  obs (mkSignal (ratio (mkRatio usage capacity hyp)) point) fidelity
saturation usage capacity nothing =
  obs (mkSignal flow point) emergent

-- error-budget consumato = bad / budget. Stessa natura di saturation: in
-- [0,1] SOLO finché non hai sforato il budget (`bad ≤ budget` è
-- falsificabile — puoi bruciare più del consentito). REGIME 2.
errorBudget : (bad budget : ℕ) → Maybe (bad ≤ budget) → Observable
errorBudget bad budget (just hyp) =
  obs (mkSignal (ratio (mkRatio bad budget hyp)) point) fidelity
errorBudget bad budget nothing =
  obs (mkSignal flow point) emergent

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  TEOREMI — il contrasto regime 1 / regime 2 vive nei tipi            ║
-- ╚══════════════════════════════════════════════════════════════════════╝

-- ── SLI: arco fedele, INCONDIZIONATO (regime emergente) ────────────────
sliIsArc     : ∀ good bad → nowReading (sli good bad) ≡ forced arc
sliIsArc _ _ = refl

sliEmergent  : ∀ good bad → Observable.regime (sli good bad) ≡ emergent
sliEmergent _ _ = refl

-- ── saturation col tetto rigido: arco, ma regime FEDELTÀ (condizionato) ─
-- Stessa FORMA dell'SLI (un arco), regime DIVERSO: l'onestà è nel campo.
satHardIsArc   : ∀ u c hyp → nowReading (saturation u c (just hyp)) ≡ forced arc
satHardIsArc _ _ _ = refl

satHardFidelity : ∀ u c hyp → Observable.regime (saturation u c (just hyp)) ≡ fidelity
satHardFidelity _ _ _ = refl

-- ── saturation senza garanzia: la gauge è RIFIUTATA ────────────────────
satSoftIsNumber : ∀ u c → nowReading (saturation u c nothing) ≡ forced number
satSoftIsNumber _ _ = refl

satSoftNotArc   : ∀ u c → nowReading (saturation u c nothing) ≢ forced arc
satSoftNotArc _ _ ()

-- ── burn-rate / latenza p99: magnitudi unbounded ⇒ MAI un arco ─────────
burnNotArc    : nowReading burnRate ≢ forced arc
burnNotArc ()

latencyQNotArc : nowReading latencyQuantile ≢ forced arc
latencyQNotArc ()
