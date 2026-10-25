# UNAPPROVED R3 archive job replacement step, for independent review only.
# Original archive adversaries and separate source-preservation/export jobs stay.
# The original historical T verifier still executes in its own unchanged
# historical Git checkout in an independently checked producing job.
# The event inputs must be collected from authentic GitHub run/job/check and
# artifact bytes. An unreviewed/absent reviewer is a hard failure.
      - name: Verify reviewed original dual T/T2 + A2 source
        shell: bash
        run: |
          set -euo pipefail
          test -s "$PERMANSSON_DUAL_HISTORICAL_EVIDENCE"
          test -s "$PERMANSSON_DUAL_ORIGINAL_T_ZIP"
          test -s "$PERMANSSON_DUAL_ORIGINAL_A2_ZIP"
          python3 -B verification/research/pr113_required_dual_gate.py \
            --evidence "$PERMANSSON_DUAL_HISTORICAL_EVIDENCE" \
            --historical-T-zip "$PERMANSSON_DUAL_ORIGINAL_T_ZIP" \
            --historical-A2-zip "$PERMANSSON_DUAL_ORIGINAL_A2_ZIP" \
            --out "$RUNNER_TEMP/pr113-historical-required-unreviewed.json"
          test -s "$RUNNER_TEMP/pr113-historical-required-unreviewed.json"
