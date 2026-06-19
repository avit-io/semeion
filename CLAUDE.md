# CLAUDE.md — semeion

## Cos'è questo progetto

semeion è una libreria **Agda** (tipi dipendenti, `--safe --without-K`) che dà
ai segnali osservabili una **geometria intrinseca**: la struttura semantica di
un segnale (dimensionalità, dominio/bounds, temporalità, comparabilità) tale
che la **visualizzazione fedele EMERGA come teorema**. L'input non è il `kind`
del widget: è la *natura* del segnale; il `kind` ne è un corollario dimostrato.

semeion è una **radice** dell'ecosistema: `depend: standard-library` e basta —
l'apeiron dei segnali, a monte di Penelope (che resta il render). semeion
produce la scelta *già dimostrata* come `Display`; **non importa Penelope** e
**non tocca JSON**.

Se per far "uscire" un widget sei tentato di stipularlo a mano accanto alla
libreria, **ti stai sbagliando**. Quello è l'antipattern che questo file
esiste per vietare.

## Regola fondamentale: proof-driven

Il flusso corretto è:

1. definisci/estendi il **tipo** della struttura del segnale (`Signal`:
   `Codomain` · `Index`);
2. enuncia i **teoremi** — quale `Display` la struttura forza;
3. **dimostrali** in Agda;
4. il `Display` (e a valle il `PanelKind` Grafana) cade fuori come *corollario*.

Il flusso vietato è il contrario: decidere il widget desiderato e poi piegare
la struttura perché lo produca. **Niente `postulate`, niente `{-# TERMINATING
#-}`, niente `trustMe`/`primTrustMe`** per zittire il checker. Se la prova è
scomoda, la prova è il punto, non l'ostacolo.

## I tre regimi — distinguili sempre

Ogni legame dato↔forma cade in uno di tre regimi, e vanno tenuti separati:

1. **emergente** (teorema) — la forma è una proprietà intrinseca della
   struttura: `ratio ∈ [0,1]` di un SLI viene da `good ≤ total` (`m≤m+n`), non
   si stipula, si *dimostra*.
2. **fedeltà** (stipulazione vincolata dal reale) — bounded solo sotto
   un'ipotesi *falsificabile* sul deployment: `saturation = usage/capacity` è
   in [0,1] solo se la capacità è un tetto rigido. L'ipotesi la fornisce
   l'operatore; il sistema può violarla.
3. **stipulazione pura** (gusto) — nessun oggetto da cui emerga, nessun fatto
   che la disciplini. Fiat.

Spacciare il regime 3 (o il 2) per il regime 1 è **disonesto**. È esattamente
ciò che semeion esiste per smascherare.

## L'onestà è nel tipo

La disonestà non deve essere *rappresentabile*:

- `Faithful = forced Display | underdetermined (List Display)` — il codominio
  di `displayAt` testimonia se la scelta è emersa. Dove la struttura non
  forza, il risultato è `underdetermined`: un menu, non una scelta travestita.
- `Regime = emergent | fidelity` (`Semeion.Vocab`) — ogni osservabile dichiara
  sotto quale regime regge il suo codominio. SLI: `emergent`. saturation /
  error-budget col tetto: `fidelity`. Stessa *forma* (un arco), regime diverso,
  nel campo.
- L'**intento** (`now`/`overTime`) è l'**unica** stipulazione, ed è il *K
  locale*: non un campo di `Signal`, ma il parametro pagato al sito d'uso.
  Sotto `--without-K` non si assume K globalmente; qui non si assume l'intento
  globalmente. Pagato l'intento, la struttura forza il resto.

Se una forma **non** emerge per una classe di segnali, **dillo**: è un
risultato, non un fallimento da mascherare. Marca la cella `underdetermined`,
o il regime `fidelity`, e spiega dove.

## Estensione conservativa

semeion si estende in modo **conservativo**:

- i teoremi già dimostrati **restano veri** dopo l'estensione (nessuna
  regressione di prove, nessun assioma aggiunto per comodità);
- un'estensione può **aggiungere** casi/segnali nuovi — mai indebolire un
  invariante esistente per far passare un caso;
- se un segnale richiede di violare la disciplina (es. marcare bounded senza
  testimone), **fermati**: o la codifica va riformulata consapevolmente, o la
  richiesta è mal posta. Un `bounded` non falsificabile è un bug, non una
  feature.

**Il README non resta a penzoloni.** Ogni estensione che cambia tipi, codifiche
o regimi aggiorna `README.md` (la sezione del tipo, la tabella `displayAt`, le
"Garanzie", "Cosa NON è garantito" e la "Roadmap") **nello stesso commit** — un
elemento di roadmap chiuso si sposta in "Già implementato". Un README che
descrive ancora la struttura vecchia è disonesto quanto una prova mascherata:
documenta una geometria che non esiste più. Lo stesso vale per i commenti-doc
dei moduli toccati.

## Le due porte (quando si lega a Penelope)

La tesi "il widget emerge invece di essere scelto" si chiude in due passi:

- **porta 1** — il kind del pannello è funzione del segnale, non un implicito
  libero (`Penelope.Semeion.panelOf`: il cancello è `displayAt i s ≡ forced
  d`). Fatta.
- **porta 2** — il `Signal` deve essere prodotto *insieme* alla query (con la
  sua prova), non asserito a fianco: la geometria **non** è derivabile dalla
  sintassi PromQL (`good ≤ total` è semantico). Si chiude per *costruzione*,
  come le foglie di un Tiling che esistono solo tagliando — non per ispezione.

Non vendere porta 1 per porta 2. Se chiudi solo la prima, **dillo**.

## Cosa consegnare

Il **sorgente `.agda`** — i tipi e le loro prove — non l'output. La cosa che si
reviewa è la prova. Ogni modulo deve typeckeckare `--safe --without-K`, **zero
`postulate`/`TERMINATING`/`trustMe`**.

Se non riesci a dimostrare che una forma emerge: **dimmi dove ti blocchi**. O
c'è un buco nella codifica (prezioso, lo chiudiamo), o quella forma davvero non
emerge (e allora è regime 2 o 3 — si nomina, non si aggira).

## Struttura

```
Semeion/
├── Signal.agda   # Signal (Codomain · Index/Dim · Temporal) · Display ·
│                 #   Determined (Faithful · QueryShape) · Intent (il K locale) ·
│                 #   displayAt + queryAt (i teoremi)
├── Vocab.agda    # vocabolario SRE: level/sli/rate/latency/burn/counter (regime 1)
│                 #   · saturation/error-budget (regime 2, fedeltà) · Regime
└── Algebra.agda  # algebra dei segnali: ⊕ / avg (i bound si compongono, regime 1 ·
                  #   Numeric) · topk (Rankable: il ranking esige comparabilità)
```

## Toolchain

Agda 2.8 via piforge, flake nix, `nix develop` (solo stdlib in scope — semeion
è una radice). Typecheck: `agda Semeion/Signal.agda`, `agda Semeion/Vocab.agda`,
`agda Semeion/Algebra.agda`.
