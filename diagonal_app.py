from flask import Flask, render_template_string, request
import random

app = Flask(__name__)

def generate_binary_table(n, cols=None):
    """Generate a table of random binary values."""
    if cols is None:
        cols = n
    return [[random.randint(0, 1) for _ in range(cols)] for _ in range(n)]

# HTML template for the web page - simplified to avoid template syntax issues
HTML_TEMPLATE = '''
<!DOCTYPE html>
<html>
<head>
    <title>The Paradox of Diagonal Arguments from a Classical Mathematics Philosophy</title>
    <style>
        body {
            font-family: Arial, sans-serif;
            margin: 40px;
            line-height: 1.6;
        }
        h1, h2, h3 {
            color: #333;
        }
        form {
            margin: 20px 0;
        }
        input[type="number"] {
            padding: 8px;
            width: 100px;
        }
        button {
            padding: 8px 15px;
            background-color: #4CAF50;
            color: white;
            border: none;
            cursor: pointer;
            border-radius: 4px;
        }
        button:hover {
            background-color: #45a049;
        }
        .binary-table {
            border-collapse: collapse;
            margin-top: 20px;
            font-family: monospace;
            font-size: 14px;
        }
        .binary-table caption {
            font-weight: bold;
            margin-bottom: 10px;
            font-size: 16px;
        }
        .binary-table th, .binary-table td {
            border: 1px solid #ddd;
            padding: 4px;
            text-align: center;
            width: 24px;
            height: 24px;
            font-size: 12px;
        }
        .binary-table th {
            background-color: #f2f2f2;
            font-weight: bold;
        }
        .diagonal-value {
            color: red;
            font-weight: bold;
        }
        .crossed-out {
            color: #666;
        }
        .crossed-out-row {
            background-color: rgba(255, 0, 0, 0.1);
            text-decoration: line-through;
        }
        .crossed-out-row th {
            background-color: rgba(255, 0, 0, 0.2);
            text-decoration: line-through;
        }
        .matching-row {
            background-color: rgba(0, 255, 0, 0.05);
        }
        .matching-row th {
            background-color: rgba(0, 255, 0, 0.1);
        }
        .instructions {
            background-color: #f8f8f8;
            padding: 15px;
            border-left: 4px solid #4CAF50;
            margin: 20px 0;
        }
        .key {
            display: inline-block;
            padding: 2px 8px;
            background-color: #f1f1f1;
            border: 1px solid #ccc;
            border-radius: 4px;
            font-family: monospace;
        }
        .error {
            color: red;
        }
        .diagonal-row {
            background-color: #f2f2f2;
        }
        .diagonal-highlight {
            background-color: #fffde7;
        }
        .table-container {
            overflow: auto;
            max-width: 100%;
            max-height: 600px;
            border: 1px solid #ddd;
        }
        .position-info {
            margin-top: 10px;
            font-style: italic;
            color: #555;
        }
        .cantor-cell {
            font-weight: bold;
            background-color: #e8eaf6;
        }
        .explanation {
            background-color: #e8f5e9;
            padding: 15px;
            border-left: 4px solid #2e7d32;
            margin: 20px 0;
        }
        .critique {
            background-color: #ffebee;
            padding: 15px;
            border-left: 4px solid #c62828;
            margin: 20px 0;
        }
        .aligned-tables {
            position: relative;
        }
        .computation-info {
            margin-top: 15px;
            color: #1976d2;
            font-weight: bold;
        }
        .eliminated-info {
            margin-top: 5px;
            color: #d32f2f;
            font-weight: bold;
        }
        .matching-info {
            margin-top: 5px;
            color: #388e3c;
            font-weight: bold;
        }
        .performance-warning {
            background-color: #fff3e0;
            padding: 10px;
            border-left: 4px solid #ff9800;
            margin: 10px 0;
            display: none;
        }
        .controls {
            margin: 20px 0;
        }
        .controls button {
            margin-right: 10px;
        }
        .display-options {
            margin: 15px 0;
        }
        .display-options label {
            margin-right: 15px;
        }
        .frozen-header th {
            position: sticky;
            top: 0;
            z-index: 2;
            background-color: #f2f2f2;
        }
        .frozen-row-numbers {
            position: sticky;
            left: 0;
            z-index: 1;
            background-color: #f2f2f2;
        }
        .cantor-row {
            position: sticky;
            top: 30px;
            background-color: #fff;
            z-index: 1;
        }
        .current-position {
            background-color: #ffecb3;
        }
        #statusBar {
            position: fixed;
            bottom: 0;
            left: 0;
            width: 100%;
            background-color: #333;
            color: white;
            padding: 5px 15px;
            text-align: left;
            display: none;
            z-index: 10;
        }
        .emphasis {
            font-weight: bold;
            text-transform: uppercase;
        }
        .conclusion {
            margin-top: 15px;
            font-style: italic;
        }
        .infinity-note {
            color: #555;
            font-style: italic;
            margin-left: 5px;
        }
    </style>
</head>
<body>
    <h1>The Paradox of Diagonal Arguments from a Classical Mathematics Philosophy</h1>
    <p>This demonstration explores the different interpretations of Cantor's Diagonal Argument when we do not remain grounded in Constructive Mathematics.</p>
    
    <form method="post">
        <label for="n">Enter the number of 100 Digit binary sequences for this demonstration (max 500):</label>
        <input type="number" id="n" name="n" min="5" max="500" value="{{ n }}">
        <button type="submit">Generate Table</button>
    </form>
    
    <div id="performanceWarning" class="performance-warning">
        <strong>Performance Note:</strong> Large table sizes may cause slower performance. Consider using values below 200 for smoother experience.
    </div>
    
    {% if error %}
    <p class="error">{{ error }}</p>
    {% endif %}
    
    {% if binary_table %}
    <div class="instructions">
        <p><strong>Interactive features:</strong></p>
        <p>Press <span class="key">Space</span> to move along the diagonal of the enumerated table and construct Cantor's diagonal sequence.</p>
        <p>For each position (i,i) in the enumerated table, the diagonal sequence value for index (i) is computed (0→1, 1→0).</p>
        <p>Enumerated sequences that differ from Cantor's constructed diagonal sequence are crossed out with a red background.</p>
        <p>Enumerated sequences that still could potentially match Cantor's sequence are highlighted in green.</p>
        <p class="position-info" id="positionInfo">Current position: Waiting to start</p>
        <p class="position-info" id="explanation">Explanation: Press space to begin</p>
        <p class="computation-info" id="computationInfo"></p>
        <p class="eliminated-info" id="eliminatedInfo"></p>
        <p class="matching-info" id="matchingInfo"></p>
    </div>
    
    <div class="controls">
        <button id="stepButton">Step (Space)</button>
        <button id="autoButton">Auto Run</button>
        <button id="resetButton">Reset</button>
    </div>
    
    <div class="display-options">
        <label>
            <input type="checkbox" id="showOnlyMatching"> Show only matching rows
        </label>
        <label>
            <input type="checkbox" id="scrollToPosition" checked> Auto-scroll to current position
        </label>
    </div>
    
    <div class="table-container aligned-tables" id="tableContainer">
        <table class="binary-table" id="binaryTable">
            <caption>An Enumerated Table of Random 100 Digit Binary Sequences</caption>
            <tr class="frozen-header">
                <th class="frozen-row-numbers"></th>
                {% for i in range(display_cols) %}
                    <th>{{ i+1 }}</th>
                {% endfor %}
            </tr>
            <tr id="cantorRow" class="cantor-row">
                <th class="frozen-row-numbers">Cantor's<br>Diagonal</th>
                {% for i in range(display_cols) %}
                    <td id="cantor-{{ i }}"></td>
                {% endfor %}
            </tr>
            {% for i in range(n) %}
                <tr id="row-{{ i }}">
                    <th class="frozen-row-numbers" id="row-header-{{ i }}">{{ i+1 }}</th>
                    {% for j in range(display_cols) %}
                        <td id="cell-{{ i }}-{{ j }}">{{ binary_table[i][j] }}</td>
                    {% endfor %}
                </tr>
            {% endfor %}
        </table>
    </div>
    
    <div id="statusBar"></div>
    
    <div class="critique">
        <h3>Cantor's Interpretation of a Diagonal Argument</h3>
        <p>Cantor claims that a diagonal argument demonstrates that the set of all unbounded binary sequences (or equivalently, the power set of natural numbers) cannot be put into a one-to-one correspondence (bijection) with the natural numbers.</p>
        <p>Key insights:</p>
        <ul>
            <li>Cantor specifies the set of all unbounded binary sequences, which can then be randomly enumerated by the natural numbers (put into a one-to-one correspondence).</li>
            <li>Cantor then specifies a diagonal sequence constructed from the given enumerated set of all unbounded binary sequences.</li>
            <li>Cantor then arbitrarily prioritizes the specified diagonal sequence, and argues that the construction of the diagonal always produces a new sequence that differs from every enumerated sequence in our set.</li>
            <li>Because the diagonal construction is generalized, it can be applied to any given enumeration and the argument remains the same.</li>
            <li>As we progress through the construction, more and more sequences are eliminated from being identical to the constructed diagonal sequence.</li>
            <li>BY THE END, no sequence in our set will match the diagonally constructed sequence.</li>
            <li>Therefore, no enumeration (one-to-one correspondence with the natural numbers) can contain all unbounded binary sequences.</li>
        </ul>
        <p class="conclusion">Cantor claims the limitation here is fundamental: no matter how many sequences are in the set of all unbounded binary sequences, we can always construct a sequence that isn't in that set.</p>
    </div>
    
    <div class="critique">
        <h3>A Different Interpretation of a Diagonal Argument</h3>
        <p>Cantor's diagonal argument fails to demonstrate that the set of all unbounded binary sequences (or equivalently, the power set of natural numbers) cannot be put into a one-to-one correspondence (bijection) with the natural numbers.</p>
        <p>Key insights:</p>
        <ul>
            <li>Cantor specifies the set of all unbounded binary sequences, which can then be randomly enumerated by the natural numbers (put into a one-to-one correspondence).</li>
            <li>Cantor then specifies a diagonal sequence constructed from the enumerated set of all unbounded binary sequences.</li>
            <li>If we arbitrarily prioritize the specification for the set of all unbounded sequences in our reasoning, then in order to claim that a constructed sequence is not in the set, we must confirm that construction sequence differs from every sequence.</li>
            <li>Because the diagonal construction is generalized, it can be applied to any given enumeration and the argument remains the same.</li>
            <li>At each computation along the diagonal, we eliminate the current sequence and we eliminate an unbounded number of enumerated binary sequences in the set.</li>
            <li><strong>HOWEVER</strong>, after any given computation to determine a value of the diagonal sequence at a given index, within the set there will always remain an unbounded number of sequences that could potentially match our diagonal construction.</li>
            <li>We always have an unbounded number of sequences that we have not proven to be distinct from our constructed diagonal, no matter how many sequences we eliminate.</li>
            <li>Therefore, the constructed diagonal is never proved to be a binary sequence that is not enumerated somewhere in the set.</li>
            <li>There is no meaning to the statement "BY THE END" as Cantor claims, from mathematical induction you must always compute another digit of the constructed diagonal to eliminate remaining sequences in your set of all binary sequences.</li>
        </ul>
        <p class="conclusion">The limitation here is fundamental: no matter how large you construct the diagonal sequence, that constructed sequence is never proved to be uniquely not in the set of all unbounded binary sequences.</p>
    </div>

    <div class="explanation">
        <h3>Philosophical Mathematical Frameworks</h3>
        <p>The classical mathematical framework accepts that specification is equivalent to implementation. However, for specified mathematical objects that are dependent upon other specified mathematical objects, we are forced to make an arbitrary choice of which specification to privilege, even if that choice is not immediately apparent.</p>
        <p>A constructive mathematical framework does not accept that specification is equivalent to implementation, and therefore avoids the necessity to arbitrarily privilege one specified object over another specified object during the construction.</p>
        <p>We lose the semantics of our mathematical language if we do not remain grounded to constructible mathematical objects.</p> 
        <ul>
            <li>The specification of an unbounded binary sequence is not itself a constructible mathematical object.</li>
            <li>The specification of the set of all unbounded binary sequences is not itself a constructible mathematical object.</li>
            <li>The specification of a constructed diagonal from an enumerated set of all unbounded binary sequences is not itself a constructible mathematical object.</li>
        </ul>
        <p>Treating specification statements as implemented mathematical objects inevitably leads to arbitrary privileging of certain specified objects over others, and therefore we can always then derive equally valid but contradicting mathematical statements.</p> 
    </div>

    <script>
        document.addEventListener('DOMContentLoaded', function() {
            // Get binary table data
            const binaryData = [
                {% for row in binary_table %}
                [
                    {% for cell in row %}
                        {{ cell }},
                    {% endfor %}
                ],
                {% endfor %}
            ];
            
            const tableSize = {{ n }};
            const displayCols = {{ display_cols }};
            let currentPosition = -1;
            let cantorSequence = [];
            let crossedOutRows = new Set();
            let autoRunInterval = null;
            
            // Show performance warning for large tables
            if (tableSize > 150) {
                document.getElementById('performanceWarning').style.display = 'block';
            }
            
            // Initialize UI controls
            document.getElementById('stepButton').addEventListener('click', updateDiagonal);
            document.getElementById('resetButton').addEventListener('click', resetDemo);
            document.getElementById('autoButton').addEventListener('click', toggleAutoRun);
            document.getElementById('showOnlyMatching').addEventListener('change', updateRowVisibility);
            
            function updateDiagonal() {
                // Cancel auto-run if we've reached the end
                if (currentPosition >= displayCols - 1) {
                    stopAutoRun();
                    return;
                }
                
                // Reset any previous diagonal highlights but keep row crossing out
                document.querySelectorAll('.diagonal-value').forEach(cell => {
                    cell.classList.remove('diagonal-value');
                });
                document.querySelectorAll('.diagonal-highlight').forEach(cell => {
                    cell.classList.remove('diagonal-highlight');
                });
                document.querySelectorAll('.current-position').forEach(cell => {
                    cell.classList.remove('current-position');
                });
                
                // Move to next diagonal position
                currentPosition++;
                
                // Stop if we've reached the end of the display columns
                if (currentPosition >= displayCols) {
                    document.getElementById('positionInfo').textContent = 'Completed: Constructed a sequence different from all ' + tableSize + ' rows';
                    document.getElementById('explanation').textContent = 'The diagonal sequence differs from every row in the table, demonstrating uncountability.';
                    
                    // Stop auto run if active
                    stopAutoRun();
                    return;
                }
                
                // Get diagonal value and its complement
                const diagonalValue = binaryData[currentPosition][currentPosition];
                const complementValue = diagonalValue === 0 ? 1 : 0;
                
                // Add to Cantor's sequence
                cantorSequence.push(complementValue);
                
                // Update UI
                const diagonalCell = document.getElementById('cell-' + currentPosition + '-' + currentPosition);
                diagonalCell.classList.add('diagonal-value');
                diagonalCell.classList.add('diagonal-highlight');
                
                // Mark current column with background
                for (let i = 0; i < tableSize; i++) {
                    if (!crossedOutRows.has(i)) { // Only highlight non-crossed out rows for performance
                        const colCell = document.getElementById('cell-' + i + '-' + currentPosition);
                        colCell.classList.add('current-position');
                    }
                }
                
                // Update Cantor's diagonal row
                const cantorCell = document.getElementById('cantor-' + currentPosition);
                cantorCell.textContent = complementValue;
                cantorCell.classList.add('cantor-cell');
                cantorCell.classList.add('current-position');
                
                // Update position info
                document.getElementById('positionInfo').textContent = 'Current position: (' + (currentPosition+1) + ', ' + (currentPosition+1) + ') - Value: ' + diagonalValue + ', Complement: ' + complementValue;
                
                // Process all rows - cross out different ones, highlight matching ones
                updateRowDisplay();
                
                // Auto-scroll to the current position if enabled
                if (document.getElementById('scrollToPosition').checked) {
                    scrollToCurrentPosition();
                }
                
                // Update status bar
                updateStatusBar();
            }
            
            function scrollToCurrentPosition() {
                const container = document.getElementById('tableContainer');
                const diagonalCell = document.getElementById('cell-' + currentPosition + '-' + currentPosition);
                
                if (diagonalCell) {
                    const cellRect = diagonalCell.getBoundingClientRect();
                    const containerRect = container.getBoundingClientRect();
                    
                    // Calculate position to ensure diagonal cell is visible
                    container.scrollLeft = diagonalCell.offsetLeft - containerRect.width / 2;
                    
                    // If position is beyond the visible area, scroll vertically
                    if (currentPosition > 10) {
                        const rowToScroll = document.getElementById('row-' + currentPosition);
                        if (rowToScroll) {
                            rowToScroll.scrollIntoView({ behavior: 'smooth', block: 'center' });
                        }
                    }
                }
            }
            
            function updateRowDisplay() {
                // For optimization with large tables, only check rows that haven't been crossed out yet
                let matchingRows = 0;
                const matchingOnly = document.getElementById('showOnlyMatching').checked;
                
                // For each row, check if it matches or differs from Cantor's sequence
                for (let rowIndex = 0; rowIndex < tableSize; rowIndex++) {
                    // Skip rows we've already crossed out
                    if (crossedOutRows.has(rowIndex)) {
                        continue;
                    }
                    
                    const row = document.getElementById('row-' + rowIndex);
                    const rowHeader = document.getElementById('row-header-' + rowIndex);
                    
                    // Remove matching class (will be re-added if still matching)
                    row.classList.remove('matching-row');
                    rowHeader.classList.remove('matching-row');
                    
                    let rowDiffersFromCantor = false;
                    
                    // Only need to check the current position since previous positions were already checked
                    if (binaryData[rowIndex][currentPosition] !== cantorSequence[currentPosition]) {
                        rowDiffersFromCantor = true;
                    }
                    
                    // If the row differs, cross it out; otherwise, highlight it as matching
                    if (rowDiffersFromCantor) {
                        crossOutRow(rowIndex);
                    } else {
                        highlightMatchingRow(rowIndex);
                        matchingRows++;
                    }
                    
                    // Handle row visibility if "show only matching" is enabled
                    if (matchingOnly) {
                        row.style.display = rowDiffersFromCantor ? 'none' : '';
                    } else {
                        row.style.display = '';
                    }
                }
                
                // Update the counters with the requested wording changes
                const computationsCompleted = currentPosition + 1;
                const totalComputations = displayCols;
                const sequencesEliminated = crossedOutRows.size;
                const sequencesNotEliminated = matchingRows;
                
                document.getElementById('computationInfo').textContent = 'Computations completed: ' + 
                    computationsCompleted + ' of ' + totalComputations + 
                    ' (or ' + computationsCompleted + ' of infinitely many computations if the table was truly All Unbounded Binary Sequences)';
                
                document.getElementById('eliminatedInfo').textContent = 'Sequences eliminated: ' + 
                    sequencesEliminated + ' of ' + tableSize + 
                    ' (or infinitely many sequences eliminated out of infinitely many sequences if the table was truly All Unbounded Binary Sequences)';
                
                document.getElementById('matchingInfo').textContent = 'Sequences not eliminated: ' + 
                    sequencesNotEliminated + ' of ' + tableSize + 
                    ' (or infinitely many sequences remain out of infinitely many sequences if table was truly All Unbounded Binary Sequences)';
            }
            
            function updateRowVisibility() {
                const showOnlyMatching = document.getElementById('showOnlyMatching').checked;
                
                // Update visibility of all rows
                for (let rowIndex = 0; rowIndex < tableSize; rowIndex++) {
                    const row = document.getElementById('row-' + rowIndex);
                    
                    if (showOnlyMatching) {
                        // Hide rows that have been crossed out
                        row.style.display = crossedOutRows.has(rowIndex) ? 'none' : '';
                    } else {
                        // Show all rows
                        row.style.display = '';
                    }
                }
            }
            
            function crossOutRow(rowIndex) {
                const row = document.getElementById('row-' + rowIndex);
                const rowHeader = document.getElementById('row-header-' + rowIndex);
                
                // Don't re-process a row that's already crossed out
                if (crossedOutRows.has(rowIndex)) {
                    return;
                }
                
                // Add to our set of crossed out rows
                crossedOutRows.add(rowIndex);
                
                // Cross out the row header
                rowHeader.classList.add('crossed-out');
                
                // Apply crossing out to the entire row (background color)
                row.classList.add('crossed-out-row');
                rowHeader.classList.add('crossed-out-row');
                
                // For visual clarity, add text decoration to all cells
                // but limit to visible area for performance in large tables
                const cellsToProcess = Math.min(currentPosition + 30, displayCols);
                for (let j = 0; j <= cellsToProcess; j++) {
                    const cell = document.getElementById('cell-' + rowIndex + '-' + j);
                    if (cell) {
                        cell.classList.add('crossed-out');
                    }
                }
            }
            
            function highlightMatchingRow(rowIndex) {
                // Skip if already crossed out
                if (crossedOutRows.has(rowIndex)) {
                    return;
                }
                
                const row = document.getElementById('row-' + rowIndex);
                const rowHeader = document.getElementById('row-header-' + rowIndex);
                
                // Add highlighting to row and header
                row.classList.add('matching-row');
                rowHeader.classList.add('matching-row');
            }
            
            function resetDemo() {
                // Stop auto-run if active
                stopAutoRun();
                
                // Reset variables
                currentPosition = -1;
                cantorSequence = [];
                crossedOutRows = new Set();
                
                // Reset UI
                document.querySelectorAll('.diagonal-value, .diagonal-highlight, .current-position').forEach(el => {
                    el.classList.remove('diagonal-value', 'diagonal-highlight', 'current-position');
                });
                
                document.querySelectorAll('.crossed-out, .crossed-out-row').forEach(el => {
                    el.classList.remove('crossed-out', 'crossed-out-row');
                });
                
                document.querySelectorAll('.matching-row').forEach(el => {
                    el.classList.remove('matching-row');
                });
                
                // Clear Cantor's sequence
                for (let i = 0; i < displayCols; i++) {
                    const cantorCell = document.getElementById('cantor-' + i);
                    cantorCell.textContent = '';
                    cantorCell.classList.remove('cantor-cell');
                }
                
                // Reset all rows to visible
                for (let i = 0; i < tableSize; i++) {
                    document.getElementById('row-' + i).style.display = '';
                }
                
                // Reset info text
                document.getElementById('positionInfo').textContent = 'Current position: Waiting to start';
                document.getElementById('explanation').textContent = 'Explanation: Press space to begin';
                document.getElementById('computationInfo').textContent = '';
                document.getElementById('eliminatedInfo').textContent = '';
                document.getElementById('matchingInfo').textContent = '';
                
                // Hide status bar
                document.getElementById('statusBar').style.display = 'none';
            }
            
            function toggleAutoRun() {
                // Clear any existing interval
                stopAutoRun();
                
                const autoButton = document.getElementById('autoButton');
                
                if (autoRunInterval) {
                    autoButton.textContent = 'Auto Run';
                } else {
                    autoButton.textContent = 'Stop Auto Run';
                    // Use a moderate speed (5 steps/sec)
                    autoRunInterval = setInterval(updateDiagonal, 200);
                    
                    // Show status bar
                    const statusBar = document.getElementById('statusBar');
                    statusBar.style.display = 'block';
                    statusBar.textContent = 'Auto run enabled: processing 5 steps per second';
                }
            }
            
            function stopAutoRun() {
                if (autoRunInterval) {
                    clearInterval(autoRunInterval);
                    autoRunInterval = null;
                    document.getElementById('autoButton').textContent = 'Auto Run';
                    document.getElementById('statusBar').style.display = 'none';
                }
            }
            
            function updateStatusBar() {
                const statusBar = document.getElementById('statusBar');
                if (autoRunInterval) {
                    const percent = Math.round((currentPosition / displayCols) * 100);
                    statusBar.textContent = 'Auto run: Position ' + (currentPosition + 1) + 
                        ' of ' + displayCols + ' (' + percent + '%) - Matching rows: ' + 
                        (tableSize - crossedOutRows.size) + ' of ' + tableSize + 
                        ' (or infinitely many of infinitely many if table was truly All Unbounded Binary Sequences)';
                    statusBar.style.display = 'block';
                }
            }
            
            // Add space bar event listener
            document.addEventListener('keydown', function(event) {
                if (event.code === 'Space') {
                    event.preventDefault(); // Prevent scrolling with space
                    updateDiagonal();
                }
            });
        });
    </script>
    {% endif %}
</body>
</html>
'''

@app.route('/', methods=['GET', 'POST'])
def index():
    binary_table = None
    error = None
    n = 10  # Default value
    display_cols = 10  # Default column display count
    
    if request.method == 'POST':
        try:
            n = int(request.form.get('n', 10))
            if n < 5:
                error = "Please enter a value of at least 5 for better visualization."
            elif n > 500:
                error = "Please use a value of 500 or less for performance reasons."
            else:
                # Limit display columns to 100 if n is larger
                display_cols = min(n, 100)
                binary_table = generate_binary_table(n, display_cols)
        except ValueError:
            error = "Invalid input. Please enter a positive integer."
    else:
        # For GET requests, generate the default table
        binary_table = generate_binary_table(n, display_cols)
    
    return render_template_string(HTML_TEMPLATE, 
                                binary_table=binary_table, 
                                error=error, 
                                n=n,
                                display_cols=display_cols)

if __name__ == '__main__':
    app.run(debug=True)
