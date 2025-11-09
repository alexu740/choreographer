module Types.Simple where
import qualified Data.Text as T
import qualified Data.Map as Map

-- | Identifiers.
type Identifier = T.Text

-- | Cell names.
type Cell = Identifier

-- | Function names.
type Function = FUNCTIONS
data FUNCTIONS
  = -- | Constructors.
    SCRYPT
  | CRYPT
  | SIGN
  | PAIR
  | SESSION
  | SID
  | XOR
  | -- | Destructors.
    DSCRYPT
  | DCRYPT
  | OPEN
  | PROJ1
  | PROJ2
  | SFST
  | SSND
  | DSID
  | -- | Verifiers.
    VSCRYPT
  | VCRYPT
  | VSIGN
  | VPAIR
  | -- | Other functions.
    INV
  | PUBK
  | HASH
    -- | Sapic specific
  | PRIV
  | ADEC
  | SDEC
  | AENC
  | SENC
  | PK
  | H
  | SK
  | MULT
  | EXP
  | G
--  | SIGN
  | VERIFY
  | REVEALSIGN
  | REVEALVERIFY
  | GETMESSAGE
  | -- | Undefined function.
    UnDef T.Text
  | CELL
  deriving (Eq, Ord, Show)

type Constructors = Map.Map FUNCTIONS Int

-- | Mode for non-deterministic choices of variables.
data Mode
  = -- | The mode \(\star\).
    Star
  | -- | The mode \(\diamond\).
    Diamond
  deriving (Eq, Show)