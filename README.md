# Group-theory-in-Coq
1. Podstawowe definicje
   - [x] Definicja typu grupy `GroupTheo` i `Group`
   - [ ] Definicja podgrupy
   - [ ] *definicja warstwy lewostronnej/prawo*

2. Proste twierdzenia dla grup i przykłady grupy i podgrupy

	- [x] a.  istnieje dokładnie jeden el neutralny `exOnlyOne`

	- [x] b. dla dowolnego el istnieje dokładnie 1 el odwrotny `exOnlyOneInv`

	- [ ] c. prawo skracania z lewej i prawej

	- [ ] d. a^-1^-1 = a

	- [ ] e. (ab)^-1 = b^-1 a^-1

	Przykład:
	- [ ] definicja grupy Z4
	- [ ] pokazać, że to grupa 
	- [ ] pokazać, że Z2 to podgrupa Z4

3. Grupy abelowe
    - [x] a. definicja grupy abelowej `AbelianGroup`
    - [ ] b. przykład, że Z3 jest abelowa.
    - [x] c. udowodnić, że grupa, w której każdy element spełnia warunek x^2 = e jest abelowa `pPowerGivesAbelian`