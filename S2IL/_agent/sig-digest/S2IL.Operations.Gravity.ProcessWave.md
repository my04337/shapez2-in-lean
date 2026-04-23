# S2IL/Operations/Gravity/ProcessWave.lean

- Lines: 503
- Declarations: 9 (theorems/lemmas: 7, defs/abbrev: 2, private: 2, sorry: 0)

## Landmarks

L10    header    # processWave 定義と終端性
L30    namespace Gravity

## Declarations

```
L43    theorem    Gravity.waveStep_layerCount_eq : (s : Shape) (h : (floatingUnits s).isEmpty = false) : (waveStep s).layerCount = s.layerCount
L91    theorem    Gravity.waveStep_grounding_mono[priv] : (s : Shape) (h : (floatingUnits s).isEmpty = false) : let fus
L251   theorem    Gravity.waveStep_ngs_strict_bound[priv] : (s : Shape) (h : (floatingUnits s).isEmpty = false) : nonGroundedLayerSum (waveStep s) + 1 ≤ nonGroundedLayerSum s
L391   theorem    Gravity.waveStep_nonGroundedLayerSum_lt : (s : Shape) (h : (floatingUnits s).isEmpty = false) : nonGroundedLayerSum (waveStep s) < nonGroundedLayerSum s
L399   def        Gravity.processWave : (s : Shape) : Shape
L411   theorem    Gravity.processWave_floatingUnits_empty : (s : Shape) : (floatingUnits (processWave s)) = []
L440   theorem    Gravity.processWave_rotate180_comm : (s : Shape) : processWave s.rotate180 = (processWave s).rotate180
L493   def        Gravity.process : (s : Shape) : Option Shape
L497   theorem    Gravity.process_of_isEmpty_floatingUnits : (s : Shape) (h : (floatingUnits s).isEmpty = true) : process s = s.normalize
```
