module SUBCONFIGURATION {
  import {
    protecting (ACZ-CONFIGURATION)
  }
  
  signature {
  [Message < Subconfiguration < ACZ-Configuration]
  }
}