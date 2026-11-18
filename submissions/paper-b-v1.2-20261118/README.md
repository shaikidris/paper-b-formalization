# Near-Linear Preprocessing for Reachability After Two Vertex Failures in Directed Acyclic Graphs

Version 1.2 by Idris Ali Shaik.

This bundle contains the Markdown source for the article and its companion, *Offline Threshold Algorithms for Two-Failure Reachability*, and their shared print stylesheet. The manuscripts use Markdown with single-backslash TeX math.

To reproduce the article’s printable HTML with Pandoc 3.9, run:

    pandoc paper-b-v1.2.md -f markdown+tex_math_single_backslash --standalone --mathml --metadata "pagetitle=Near-Linear Preprocessing for Reachability After Two Vertex Failures in Directed Acyclic Graphs" -H print-style.html -o paper-b-v1.2.html

Open the HTML in Chrome and print to PDF with browser headers and footers disabled. Use the companion’s filename and title to reproduce its PDF.
