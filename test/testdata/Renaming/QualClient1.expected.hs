module Renaming.QualClient1 where

import qualified Renaming.QualServer1 as QS

foo :: QS.T
foo = QS.T { QS.field1 = 3 }

