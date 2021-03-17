
# Installation requirements
- Why3 1.3.3
- Z3 4.7.1
- Easycrypt Git hash ddb426b596c97417989ff28cf3f382649caee4af
  - It is recommended to run ```easycrypt why3config``` to set up the smt solvers.

# About the files
## Decomposition.eca
Defines the abstraction notion of a decompostion protocol and they security defintions.

## Commitment.eca
Defines security of commitments schemes (With no secret keys)

## SigmaProtocols.eca
Security definitions of Sigma-Protocols

## Folding
General lemmas about foldr

## ZKBooDecomposition
An implementation of the ZKBoo MPC protocol, following the notion of decomposition protocols from ```Decomposition.eca```.

## ZKBooTransformation
A valid instance of a Sigma-Protocol, based on the ZKBoo Sigma-Protocol, showing security based on any decomposition satifying the security definitions.
