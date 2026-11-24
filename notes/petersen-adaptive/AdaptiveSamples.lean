import AdaptiveData
namespace PetersenOrientation.Replay
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem finalRow : checkRow 9 0 = true := by decide +kernel
theorem firstRow : checkRow 14 0 = true := by decide +kernel
end PetersenOrientation.Replay
#print axioms PetersenOrientation.Replay.finalRow
#print axioms PetersenOrientation.Replay.firstRow
