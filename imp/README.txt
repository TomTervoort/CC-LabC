Compiler Construction - Mini Project C

Bas du Pré   - 3310566
Tom Tervoort - 3470784

============================================

Installatie, documentatie, tests:

Het geheel kan gewoon gebouwd worden via cabal. De aangepaste .ag-file is al geprocessed.

Haddock-documentatie is te vinden in de doc-map. Tests staan in de test-map. De .ssm-files in deze 
map bevatten de SSM-code die gegenereerd is d.m.v. de gegeven, nog niet geoptimaliseerde, 
generator. De .new.ssm-files bevatten de output van de nieuwe generator met static-link 
optimalisatie.

Tests 0 t/m 4 zijn als gegeven. Test 5 en 6 zijn toegevoegd.


============================================

Aanpassingen aan de code:

Alle aanpassingen en toevoegingen zijn gedaan in de AG source file CCO/Imp/AG/CodeGeneration.ag.

- Toevoeging twee simpele helper-functies: (<<$) en composeList.
- Functies loadSLCache en unloadSLCache, die respectievelijk het stuk stack dat gebruikt wordt 
  voor de static-link cache initialiseren en vernietigen. De functie wrapSLCacheLoader vouwt een 
  loader en unloader om een ander stuk code heen.
- De semantische regels voor Call_ statements en Call expressies zijn uitgebreid met het gebruik 
  van wrapSLCacheLoader.
- De functie getLink is toegevoegd: deze genereert een stuk code om het static link-adres, dat 
  verwijst naar de scope van een bepaalde variabele, te verkrijgen. Ook wordt getelt hoeveel
  scopes teruggestapt moet worden hiervoor. Alle static-link traversals die nog worden uitgevoerd 
  zijn afkomstig van deze functie.
- De functies getGlobal en setGlobal zijn vervangen door getCached en setCached: deze springen 
  naar de locatie van de te lezen of schrijven variabele op basis van een gecacht adres en voeren
  dus zelf geen static-link traversal meer uit. Beide functies gebruiken de helper withCached.
- get en set zijn aangepast om getCached en setCached te gebruiken.
- De functie cacheVars wordt gebruikt door loadSLCache om te bepalen welke variabelen bereikbaar 
  dienen te zijn vanuit een bepaalde omgeving. Dit wordt gedaan door simpelweg alle bereikbare 
  variabelen te filteren op basis van de context.

============================================

Aanpak gecachte petatraversal:

- De traversals worden toegepast voor het uitvoeren van een functie-call. De cache van static links naar blokken variabelen worden net voor de waarden van de parameters van een functie op de 
stack gepusht.
- De functie cacheVars (zie hieronder) bepaalt naar welke variabelen een gecachte link dient te 
bestaan. Van deze variabelen wordt gekeken in welke scope ze staan en enkel van die scopes wordt 
de link in de cache geplaatst.
- Wanneer get of set wordt aangeroepen en de gewenste variabele niet lokaal beschikbaar is, wordt 
  de traversal gestart vanaf de gecachte link die hoort bij deze variabele. 


============================================

Filteren van onnodige variabelen: