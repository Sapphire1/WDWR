#########
# MODEL #
#########

param PRODUKT;
param MASZYNA;
param NR_MASZYNY {1 .. MASZYNA};
param DZIEN;
param ZMIANA;
param MIESIAC;
param DLUGOSC_ZMIANY;
param EPSILON;
param ILOSC_ZMIAN;
param CZAS_PRODUKCJI {1 .. PRODUKT, 1 .. MASZYNA};
param CZY_PRODUKUJEMY {1 .. PRODUKT, 1 .. MASZYNA};
param KOSZT_MAGAZYNOWANIA;
param LAMBDA;
param R {1 .. MIESIAC, 1 .. PRODUKT};
param LIMIT_PROD {1 .. MIESIAC, 1 .. PRODUKT};
param WAR_OCZEKIWANA{1 .. PRODUKT};

### daty przechowywania materiałów w magazynie
# 1 - przed styczniem
# 2 - między styczniem a lutym
# 3 - między lutym a marcem
# 4 - po marcu
###
param OKRES;

param MIN_MAGAZYN;
param MAX_MAGAZYN;
param STAN_MAGAZYNU_KONIEC;

### ZMIENNE

# wyprodukowana_ilosc wytworzonego produktu na danych maszynach w konkretnym terminie
var x 
{
1	..	PRODUKT,
n in 1	..	MASZYNA,
1	..	NR_MASZYNY[n],
1	..	DZIEN,
1	..	ZMIANA,
1	..	MIESIAC 
}, integer, >= 0;

# czy maszyna pracuje na danej zmianie
var y 
{
n in 1	..	MASZYNA,
1	..	NR_MASZYNY[n],
1	..	DZIEN,
1	..	ZMIANA,
1	..	MIESIAC 
}, binary;

var d_zm, integer;

# ilosc wyprodukowanego przedmiotu
var wyprodukowana_ilosc{1 .. PRODUKT, 1 .. MIESIAC}, integer, >= 0;

# ilosc przedmiotow wystawionych na sprzedaz
var ilosc_na_sprzedaz{1 .. PRODUKT, 1 .. MIESIAC}, integer, >= 0;

# towar magazynowany
var magazyn{1 .. PRODUKT, 1 .. OKRES}, integer;
var binary_magazyn{1 .. PRODUKT, 1 .. OKRES}, binary;

##########
# F CELU #
##########

maximize zysk:
sum{p in 1 .. PRODUKT, m in 1 .. MIESIAC}(
WAR_OCZEKIWANA[p]*ilosc_na_sprzedaz[p,m] -LAMBDA*d_zm- magazyn[p,m + 1] * KOSZT_MAGAZYNOWANIA);

################
# OGRANICZENIA #
################

### PRODUKCJA
subject to produkcja_w_ciagu_zmiany
{
n in 1 .. MASZYNA,
nm in 1 .. NR_MASZYNY[n],
d in 1 .. DZIEN,
z in 1 .. ZMIANA,
m in 1 .. MIESIAC
}:
sum{p in 1 .. PRODUKT} x[p,n,nm,d,z,m] * CZAS_PRODUKCJI[p,n] <= DLUGOSC_ZMIANY;

subject to ilosc_wyprodukowanych_przedmiotow
{p in 1 .. PRODUKT,n in 1 .. MASZYNA, m in 1 .. MIESIAC }:
wyprodukowana_ilosc[p,m] * CZY_PRODUKUJEMY[p,n] = CZY_PRODUKUJEMY[p,n] * 
sum{nm in 1 .. NR_MASZYNY[n], d in 1 .. DZIEN, z in 1 .. ZMIANA} x[p,n,nm,d,z,m];


### SPRZEDAZ
subject to ilosc_sprzedawanych_przedmiotow
{p in 1 .. PRODUKT, m in 1 .. MIESIAC }:
ilosc_na_sprzedaz[p,m] = wyprodukowana_ilosc[p,m] - magazyn[p,m + 1] +  magazyn[p,m];

subject to ilosc_sprzedawanych_przedmiotow_1
{p in 1 .. PRODUKT, m in 1 .. MIESIAC }:
ilosc_na_sprzedaz[p,m] <= LIMIT_PROD[m,p];

### OBSLUGA MAGAZYNU ###
subject to magazynowanie_poczatek
{p in 1 .. PRODUKT}: magazyn[p,1] = 0;

subject to magazynowanie_koniec
{p in 1 .. PRODUKT }:
magazyn[p,4] = STAN_MAGAZYNU_KONIEC;

subject to magazynowanie_semi_cond_1
{p in 1 .. PRODUKT, o in 2 .. (OKRES - 1) }:
binary_magazyn[p,o] * MIN_MAGAZYN <= magazyn[p,o];

subject to magazynowanie_semi_cond_2
{p in 1 .. PRODUKT, o in 2 .. (OKRES - 1) }:
magazyn[p,o] <= binary_magazyn[p,o] * MAX_MAGAZYN;


### WYLACZANIE MASZYN W CZASIE ZMIANY
subject to maszyny_konserwacja_semi_cond_1
{n in 1 .. MASZYNA, nm in 1 .. NR_MASZYNY[n], d in 1 .. DZIEN, z in 1 .. ZMIANA, m in 1 .. MIESIAC }:
y[n,nm,d,z,m] * EPSILON <= (sum{p in 1 .. PRODUKT} x[p,n,nm,d,z,m]) ;

subject to maszyny_konserwacja_semi_cond_2
{n in 1 .. MASZYNA, nm in 1 .. NR_MASZYNY[n], d in 1 .. DZIEN, z in 1 .. ZMIANA, m in 1 .. MIESIAC }:
(sum{p in 1 .. PRODUKT} x[p,n,nm,d,z,m] * CZAS_PRODUKCJI[p,n]) <= y[n,nm,d,z,m] * DLUGOSC_ZMIANY;

subject to maszyny_konserwacja_2
{ n in 1 .. MASZYNA }:
sum{nm in 1 .. NR_MASZYNY[n], d in 1 .. DZIEN, z in 1 .. ZMIANA, m in 1 .. MIESIAC} 
y[n,nm,d,z,m] <= (NR_MASZYNY[n] * ILOSC_ZMIAN) - 1 ;

subject to d_zm_1
{m in 1 .. MIESIAC }:
(sum{p in 1 .. PRODUKT} (WAR_OCZEKIWANA[p]-R[m,p])*ilosc_na_sprzedaz[p,m])<=d_zm;

subject to d_zm_2
{m in 1 .. MIESIAC }:
(sum{p in 1 .. PRODUKT} (R[m,p]-WAR_OCZEKIWANA[p])*ilosc_na_sprzedaz[p,m])<=d_zm;