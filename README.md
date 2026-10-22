# pada
Solveur kangaroo

# Kangaroo secp256k1 – Tame précalculés

Solveur de logarithme discret sur secp256k1 dans un intervalle [1, 2^B]
(B = 80 par défaut) par Pollard Kangaroo.

L'idée : on précalcule une fois des points distingués « Tame », on les
sauvegarde, puis on les réutilise pour résoudre une ou plusieurs clés
publiques avec des kangourous « Wild » (effort bien plus faible).

## Fonctionnement
- Symétrie ± (classe {P, −P}, parité de y)
- Collisions Tame/Wild et Wild/Wild de signes opposés
- Inversion modulaire par lots (Montgomery), détection de cycles courts
- Arithmétique 4×64 bits, multi-thread
- Points distingués sauvegardés dans `tame_NNN.dp` (32 octets / point)

## Modes
1. Créer un fichier Tame
2. Continuer un fichier Tame (Ctrl+C = sauvegarde propre)
3. Charger un fichier Tame et résoudre une ou plusieurs clés publiques

## Compilation (64 bits, GCC/Clang avec `__int128`)
- Linux : `g++ -O3 -march=native -std=c++17 -pthread kangaroo.cpp -o kangaroo`
- Termux : `pkg install clang` puis
  `clang++ -O3 -std=c++17 -pthread kangaroo.cpp -o kangaroo`
- Windows (MSYS2 MinGW-w64) :
  `g++ -O3 -march=native -std=c++17 -pthread -static kangaroo.cpp -o kangaroo.exe`
- Visual Studio (MSVC) n'est pas supporté.

## Utilisation
- Test : `./kangaroo --selftest`
- Créer : `./kangaroo -m 1 -r 80 -d 21 -n 8388608`
- Continuer : `./kangaroo -m 2 -f 1 -n 8388608`
- Résoudre : `./kangaroo -m 3 -f 1 -k <clé_publique_hex>`
- Clé publique de test : `./kangaroo --pub 0x8a1b2c3d4e`

La solution s'affiche et s'ajoute à `solution.txt`.

## Compromis Tame / Wild (intervalle 2^80)
| Tame stockés | Wild moyen |
|---|---|
| 0,5 √N | ~1 √N |
| 1 √N | ~0,5 √N |
| 4 √N | ~0,12 √N |
| 16 √N | ~0,03 √N |

Estimations (κ ≈ 1 mesuré à 2^40, bruit ~10 %). Le total pour une seule
clé est d'environ 1,5 √N ; un grand Tame n'est utile que pour plusieurs clés.

## Limites
- CPU uniquement (pas de GPU).
- Testé sur 1 cœur jusqu'à 2^40 ; Termux testé en démarrage seulement.
- Un seul fichier Tame par résolution (pas de fusion).
- Ne jamais publier `solution.txt` ni les fichiers `.dp`.


Avant de lancer
termux-wake-lock : empêche Android de suspendre Termux (dans un autre onglet).
df -h . : vérifie la place disponible.
Compiler (déjà fait)
clang++ -O3 -std=c++17 -pthread pada.cpp -o pada
Mode 1 : créer le fichier Tame (16√N)
./pada -m 1 -r 80 -d 21 -n 8388608
Appuie sur Entrée à chaque question, puis une dernière fois pour démarrer.
Ctrl+C pour arrêter et sauvegarder.
Mode 2 : reprendre
./pada -m 2 -f 1 -n 8388608
Entrée aux questions.
-f 1 correspond à tame_001.dp.
Mode 3 : résoudre une clé
./pada -m 3 -f 1
Colle ta clé publique (hex, compressée ou non) quand il la demande, puis Entrée pour les threads.
Pour plusieurs clés : mets-les dans un fichier texte (une par ligne) et donne son nom à la place de la clé.
Variante en une ligne : ./pada -m 3 -f 1 -k <clé_publique>
Le résultat s'affiche et s'ajoute à solution.txt.
Utiles
ls -l tame_*.dp : voir tes fichiers et leur taille.
cat solution.txt : relire les clés trouvées.
./pada --pub 0x8a1b2c3d4e : calcule une clé publique de test.
./pada --selftest : vérifie que le calcul est correct sur ton téléphone.

kaggle

!git clone https://github.com/lawahakassou-tech/pada.git
%cd pada
!g++ -O3 -march=native -std=c++17 -pthread pada.cpp -o pada && ./pada --selftest


