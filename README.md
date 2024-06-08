# Group-theory-in-Coq
1. Podstawowe definicje
   - [x] Definicja typu grupy `GroupTheo` i `Group` (Zuzia)
   - [x] Definicja podgrupy `Section Subgroup`	(Krzysztof)
   - [ ] *definicja warstwy lewostronnej/prawo*

2. Proste twierdzenia dla grup i przykłady grupy i podgrupy

	- [x] a.  istnieje dokładnie jeden el neutralny `exOnlyOne` (Zuzia)

	- [x] b. dla dowolnego el istnieje dokładnie 1 el odwrotny `exOnlyOneInv` (Zuzia)

	- [x] c. prawo skracania z lewej i prawej `cancelL` i `cancelR` (Krzysztof)

	- [x] d. a^-1^-1 = a `InvInvAIsA` (Krzysztof)

	- [x] e. (ab)^-1 = b^-1 a^-1 `InvABEqInvBInvA` (Krzysztof)

	Przykład: 
	- [x] definicja grupy Z4 `Section Z4_Group` (Krzysztof)
	- [x] pokazać, że to grupa 
	- [ ] pokazać, że Z2 to podgrupa Z4

3. Grupy abelowe
    - [x] a. definicja grupy abelowej `AbelianGroup` (Zuzia)
    - [ ] b. przykład, że Z3 jest abelowa.
    - [x] c. udowodnić, że grupa, w której każdy element spełnia warunek x^2 = e jest abelowa `pPowerGivesAbelian` (Zuzia)
