# Increment 2 producer bytes (history)

`native_slice.py` (sha256 `633bec1ecd4d6bfb8ba68077515be7880380b7b001e069d4efd67b2c38f4f203`)
and `nullcount_scan.py` are the exact version-1 producers of the records in this
directory. They are preserved byte for byte so every Increment 2 record stays
bound to the code that produced it. Their acceptance logic is **superseded**: see
[CORRECTIONS.json](../../increment2b/CORRECTIONS.json) (findings R1–R9) and the
version-2 engine with the numpy-free kernel `certificates.py`. Do not use them
for new results. RH and Step 4 remain OPEN.
