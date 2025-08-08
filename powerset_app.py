from flask import Flask, render_template_string, request
import math
from itertools import combinations

app = Flask(__name__)

def generate_powerset_pattern(n):
    """Generate rows of power sets according to the specified pattern."""
    table_data = []
    
    # Pre-define the patterns for rows 1-8
    patterns = {
        1: ["∅", "{1}"],
        2: ["∅", "{1}", "{2}", "{1, 2}"],
        3: ["∅", "{1}", "{2}", "{1, 2}", "{3}", "{1, 3}", "{2, 3}", "{1, 2, 3}"],
        4: ["∅", "{1}", "{2}", "{1, 2}", "{3}", "{1, 3}", "{2, 3}", "{1, 2, 3}", 
            "{4}", "{1, 4}", "{2, 4}", "{1, 2, 4}", "{3, 4}", 
            "{1, 3, 4}", "{2, 3, 4}", "{1, 2, 3, 4}"],
        5: ["∅", "{1}", "{2}", "{1, 2}", "{3}", "{1, 3}", "{2, 3}", "{1, 2, 3}",
            "{4}", "{1, 4}", "{2, 4}", "{1, 2, 4}", "{3, 4}", 
            "{1, 3, 4}", "{2, 3, 4}", "{1, 2, 3, 4}", "{5}", "{1, 5}", 
            "{2, 5}", "{1, 2, 5}", "{3, 5}", "{1, 3, 5}", "{2, 3, 5}", 
            "{1, 2, 3, 5}", "{4, 5}", "{1, 4, 5}", "{2, 4, 5}", 
            "{1, 2, 4, 5}", "{3, 4, 5}", "{1, 3, 4, 5}", "{2, 3, 4, 5}", 
            "{1, 2, 3, 4, 5}"]
    }
    
    # For rows 6-8, generate programmatically
    if n > 5:
        for i in range(6, n+1):
            # Start with the pattern from the previous row
            pattern_i = patterns[i-1].copy()
            
            # Add all subsets containing the new element i
            all_subsets = []
            for size in range(1, i+1):
                for combo in combinations(range(1, i+1), size):
                    if i in combo:
                        all_subsets.append("{" + ", ".join(str(x) for x in combo) + "}")
            
            # Add all subsets containing i that weren't in the previous row
            for subset in all_subsets:
                if subset not in pattern_i:
                    pattern_i.append(subset)
            
            patterns[i] = pattern_i
    
    # Create rows using the patterns
    for i in range(1, n+1):
        row = patterns[i].copy()
        
        # Fill the rest with empty sets to match the required length
        remaining = (1 << n) - len(row)
        for _ in range(remaining):
            row.append("∅")
            
        table_data.append(row)
    
    return table_data

# Generate the row labels in the format {1}, {1,2}, etc.
def generate_row_labels(n):
    labels = []
    for i in range(1, n+1):
        elements = range(1, i+1)
        label = "{" + ", ".join(str(x) for x in elements) + "}"
        labels.append(label)
    return labels

# HTML template for the web page
HTML_TEMPLATE = '''
<!DOCTYPE html>
<html>
<head>
    <title>Bijection from the Natural Numbers to the Power Set of the Natural Numbers</title>
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
        .main-container {
            display: flex;
            gap: 30px;
            flex-wrap: wrap;
        }
        .table-container {
            display: flex;
            gap: 30px;
            margin-top: 20px;
            align-items: flex-start;
        }
        .powerset-table {
            border-collapse: collapse;
            margin-top: 20px;
        }
        .powerset-table-container {
            overflow-x: auto;
            max-width: 100%;
            margin-bottom: 20px;
        }
        .powerset-table th, .powerset-table td {
            border: 1px solid #ddd;
            padding: 8px;
            text-align: center;
            min-width: 80px;
        }
        .powerset-table th {
            background-color: #f2f2f2;
            font-weight: bold;
            position: sticky;
            left: 0;
            z-index: 1;
        }
        .element-highlight {
            color: red;
            font-weight: bold;
        }
        .error {
            color: red;
        }
        .history-table, .bijection-table {
            border-collapse: collapse;
            min-width: 200px;
        }
        .history-table th, .history-table td,
        .bijection-table th, .bijection-table td {
            border: 1px solid #ddd;
            padding: 8px 12px;
            text-align: left;
        }
        .history-table th, .bijection-table th {
            background-color: #f2f2f2;
            position: sticky;
            top: 0;
        }
        .history-container, .bijection-container {
            max-height: 500px;
            overflow-y: auto;
            border: 1px solid #ddd;
        }
        .instructions {
            background-color: #f8f8f8;
            padding: 10px;
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
        .position-info {
            margin-top: 10px;
            font-style: italic;
            color: #555;
        }
        .current-step {
            font-weight: bold;
            background-color: #e8f4ff;
        }
        .panel {
            flex: 1;
            min-width: 350px;
            margin-bottom: 20px;
        }
        .panel-title {
            margin-bottom: 10px;
            border-bottom: 1px solid #ddd;
            padding-bottom: 5px;
        }
        .warning {
            background-color: #fff3cd;
            color: #856404;
            padding: 10px;
            margin: 10px 0;
            border-left: 4px solid #ffeeba;
        }
        .new-entry {
            background-color: #e8f4ff;
            font-weight: bold;
        }
    </style>
</head>
<body>
    <h1>Bijection from the Natural Numbers to the Power Set of the Natural Numbers</h1>
    <p>Enter a positive integer to generate the table of power sets.</p>
    
    <form method="post">
        <label for="n">Enter a value between 1 and 8:</label>
        <input type="number" id="n" name="n" min="1" max="8" value="{{ n }}">
        <button type="submit">Generate Table</button>
    </form>
    
    {% if n > 5 %}
    <div class="warning">
        <strong>Note:</strong> For values of n > 5, the table will be quite large. You may need to scroll horizontally to see all elements.
    </div>
    {% endif %}
    
    {% if error %}
    <p class="error">{{ error }}</p>
    {% endif %}
    
    {% if table_data %}
    <div class="instructions">
        <p><strong>Interactive features:</strong></p>
        <p>Press <span class="key">Space</span> to move through the elements row by row.</p>
        <p>The traversal will skip to the next row when only empty sets remain in the current row.</p>
        <p>The current element will appear in red in the table and be recorded in the history panel.</p>
        <p>The bijection mapping starts with 1 ↔ ∅ and continues with unique sets found during traversal.</p>
        <p class="position-info" id="positionInfo">Current set: -</p>
        <p class="position-info" id="rowInfo">Current row: -</p>
    </div>
    
    <div class="main-container">
        <!-- Left side: Power Set table -->
        <div class="panel">
            <h2 class="panel-title">Table of Power Sets</h2>
            <div class="powerset-table-container">
                <table class="powerset-table" id="powersetTable">
                    <tr>
                        <th>Row</th>
                        {% for j in range((2**n)) %}
                            <td>{{ j+1 }}</td>
                        {% endfor %}
                    </tr>
                    {% for i in range(n) %}
                        <tr>
                            <th>{{ row_labels[i] }}</th>
                            {% for j in range((2**n)) %}
                                <td id="cell-{{ i+1 }}-{{ j+1 }}">{{ table_data[i][j] }}</td>
                            {% endfor %}
                        </tr>
                    {% endfor %}
                </table>
            </div>
        </div>
        
        <!-- Right side: History and Bijection -->
        <div class="panel">
            <h2 class="panel-title">Traversal Data</h2>
            
            <div class="table-container">
                <!-- History panel -->
                <div>
                    <h3>History Log</h3>
                    <div class="history-container">
                        <table class="history-table" id="historyTable">
                            <thead>
                                <tr>
                                    <th>#</th>
                                    <th>Set</th>
                                </tr>
                            </thead>
                            <tbody id="historyBody">
                                <!-- History entries will be added here -->
                            </tbody>
                        </table>
                    </div>
                </div>
                
                <!-- Bijection panel -->
                <div>
                    <h3>Bijection Mapping</h3>
                    <div class="bijection-container">
                        <table class="bijection-table" id="bijectionTable">
                            <thead>
                                <tr>
                                    <th>ℕ</th>
                                    <th>Power Set</th>
                                </tr>
                            </thead>
                            <tbody id="bijectionBody">
                                <tr>
                                    <td>1</td>
                                    <td>∅</td>
                                </tr>
                                <!-- Additional bijection entries will be added here -->
                            </tbody>
                        </table>
                    </div>
                </div>
            </div>
        </div>
    </div>

    <script>
        document.addEventListener('DOMContentLoaded', function() {
            // Get the organized row data
            const rowData = [
                {% for row in table_data %}
                [
                    {% for set in row %}
                        "{{ set }}",
                    {% endfor %}
                ],
                {% endfor %}
            ];
            
            const rowLabels = [
                {% for label in row_labels %}
                    "{{ label }}",
                {% endfor %}
            ];
            
            let currentRowIndex = 0;
            let currentElementIndex = 0;
            let history = [];
            let bijectionCounter = 2; // Start at 2 since 1 is already mapped to empty set
            let uniqueSets = new Set(["∅"]); // Already include empty set
            let lastAddedBijectionRow = null;
            
            function getCurrentElement() {
                if (currentRowIndex < rowData.length && 
                    currentElementIndex < rowData[currentRowIndex].length) {
                    return rowData[currentRowIndex][currentElementIndex];
                }
                return null;
            }
            
            function updateHighlight() {
                // Clear all highlights
                document.querySelectorAll('.powerset-table td').forEach(cell => {
                    cell.classList.remove('element-highlight');
                });
                
                // Remove new-entry class from previously added bijection row
                if (lastAddedBijectionRow) {
                    lastAddedBijectionRow.classList.remove('new-entry');
                }
                
                const currentElement = getCurrentElement();
                if (!currentElement) return;
                
                // Update position info display
                document.getElementById('positionInfo').textContent = `Current set: ${currentElement}`;
                document.getElementById('rowInfo').textContent = `Current row: ${rowLabels[currentRowIndex]}`;
                
                // Find and highlight the current cell
                const cellId = `cell-${currentRowIndex+1}-${currentElementIndex+1}`;
                const cell = document.getElementById(cellId);
                if (cell) {
                    cell.classList.add('element-highlight');
                }
                
                // Add to history
                history.push({
                    step: history.length + 1,
                    set: currentElement
                });
                
                // Update history table
                updateHistoryTable();
                
                // Update bijection table only if this is a unique non-empty set
                // (We already have the empty set in the bijection)
                if (!uniqueSets.has(currentElement)) {
                    uniqueSets.add(currentElement);
                    lastAddedBijectionRow = updateBijectionTable(currentElement);
                }
            }
            
            function updateHistoryTable() {
                const historyBody = document.getElementById('historyBody');
                
                // Clear existing rows first
                historyBody.innerHTML = '';
                
                // Add all history entries
                history.forEach((entry, index) => {
                    const row = document.createElement('tr');
                    if (index === history.length - 1) {
                        row.classList.add('current-step');
                    }
                    
                    row.innerHTML = `
                        <td>${entry.step}</td>
                        <td>${entry.set}</td>
                    `;
                    
                    historyBody.appendChild(row);
                });
                
                // Scroll to the bottom of history container
                const historyContainer = document.querySelector('.history-container');
                historyContainer.scrollTop = historyContainer.scrollHeight;
            }
            
            function updateBijectionTable(value) {
                const bijectionBody = document.getElementById('bijectionBody');
                
                const row = document.createElement('tr');
                row.classList.add('new-entry');
                
                row.innerHTML = `
                    <td>${bijectionCounter}</td>
                    <td>${value}</td>
                `;
                
                bijectionBody.appendChild(row);
                bijectionCounter++;
                
                // Scroll to the bottom of bijection container
                const bijectionContainer = document.querySelector('.bijection-container');
                bijectionContainer.scrollTop = bijectionContainer.scrollHeight;
                
                return row;
            }
            
            function shouldSkipToNextRow() {
                // Check if all remaining elements in this row are empty sets
                for (let i = currentElementIndex; i < rowData[currentRowIndex].length; i++) {
                    if (rowData[currentRowIndex][i] !== "∅") {
                        return false;
                    }
                }
                return true;
            }
            
            function movePosition() {
                // Move to the next element in the current row
                currentElementIndex++;
                
                // If all remaining elements in the current row are empty sets, skip to next row
                if (shouldSkipToNextRow()) {
                    currentElementIndex = 0;
                    currentRowIndex++;
                    
                    // If we've gone through all rows, go back to the first row
                    if (currentRowIndex >= rowData.length) {
                        currentRowIndex = 0;
                    }
                }
                
                // If we've reached the end of the current row
                if (currentElementIndex >= rowData[currentRowIndex].length) {
                    currentElementIndex = 0;  // Reset to start of row
                    currentRowIndex++;        // Move to next row
                    
                    // If we've gone through all rows, go back to the first row
                    if (currentRowIndex >= rowData.length) {
                        currentRowIndex = 0;
                    }
                }
                
                updateHighlight();
            }
            
            // Initialize the first highlight and history
            if (rowData.length > 0 && rowData[0].length > 0) {
                updateHighlight();
            }
            
            // Add space bar event listener
            document.addEventListener('keydown', function(event) {
                if (event.code === 'Space') {
                    event.preventDefault(); // Prevent scrolling with space
                    movePosition();
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
    table_data = None
    error = None
    n = 3  # Default value
    row_labels = []
    
    if request.method == 'POST':
        try:
            n = int(request.form.get('n', 3))
            if n < 1:
                error = "Please enter a value of at least 1."
            elif n > 8:
                error = "Please use a value of 8 or less due to the exponential growth of the power set."
            else:
                table_data = generate_powerset_pattern(n)
                row_labels = generate_row_labels(n)
        except ValueError:
            error = "Invalid input. Please enter a positive integer."
    else:
        # For GET requests, generate the default table
        table_data = generate_powerset_pattern(n)
        row_labels = generate_row_labels(n)
    
    return render_template_string(HTML_TEMPLATE, table_data=table_data, row_labels=row_labels, error=error, n=n)

if __name__ == '__main__':
    app.run(debug=True)
