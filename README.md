# Forest

[Forest](Forest.v) frames the basic definitions of RNmatrix [1] in Coq. Building upon this, we implemented the following logics:

1. [Cn](Cn/Cn1.v) via the RNmatrix described in [1] for the family of da Costa's paraconsistent logics $C_n$.
2. [T](T/T1.v) via the RNmatrix described in [2] for the modal logic **T**.
3. [S4](S4/S41.v) via the RNmatrix described in [2] for the modal logic **S4**.
4. [IPL](IPL/IPL1.v) via the RNmatrix described in [3] for the intuitionistic propositional logic.
5. [IPL](IPL/IPL2.v) via the RNmatrix described in [4] for the intuitionistic propositional logic.

To run with default examples, open the root folder inside some terminal.  In the terminal, run:

```bash
chmod +x Run.sh
```

Then:

```bash
./Run.sh <logic> <implementation>
```

Where `<logic>` is one of the following:

- `Cn`
- `T`
- `S4`
- `IPL`

and `<implementation>` is one of the following:

- `1`
- `2`
- etc.

Examples:

```bash
./Run.sh Cn 1
```

```bash
./Run.sh IPL 2
```

Please look inside of each file for specific orientations about how to run with different examples.

## Requirements

- Coq 8.13.2 or later.

# References

1. CONIGLIO, Marcelo E.; TOLEDO, Guilherme V. Two Decision Procedures for da Costa’s C n Logics Based on Restricted Nmatrix Semantics. Studia Logica, v. 110, n. 3, p. 601-642, 2022.
2. GRÄTZ, Lukas. Truth tables for modal logics T and S4, by using three-valued non-deterministic level semantics. Journal of Logic and Computation, v. 32, n. 1, p. 129-157, 2022.
3. LEME, Renato; CONIGLIO, Marcelo; LOPES, Bruno. Intuitionism with Truth Tables: A Decision Procedure for IPC Based on RNMatrix. arXiv preprint arXiv:2308.13664, 2023.
4. TRACTABLE DEPTH-BOUNDED APPROXIMATIONS TO SOME PROPOSITIONAL LOGICS. TOWARDS MORE REALISTIC MODELS OF LOGICAL AGENTS / A.j. Solares Rojas ; supervisore: A. Zamansky, M. D'Agostino ; coordinatore: A. Pinotti. Dipartimento di Filosofia Piero Martinetti, 2022 Jul 15. 34. ciclo, Anno Accademico 2021.