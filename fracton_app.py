from flask import Flask, render_template_string, request
import math

app = Flask(__name__)

def gcd(a, b):
    """Calculate the greatest common divisor of a and b."""
    while b:
        a, b = b, a % b
    return a

def reduce_fraction(numerator, denominator):
    """Reduce a fraction to its simplest form."""
    if denominator == 0:
        return "undefined"
    
    if numerator == 0:
        return "0"
        
    # Find the greatest common divisor
    divisor = gcd(abs(numerator), abs(denominator))
    
    # Reduce the fraction
    numerator //= divisor
    denominator //= divisor
    
    # Handle negative denominators
    if denominator < 0:
        numerator, denominator = -numerator, -denominator
        
    # Return string representation
    if denominator == 1:
        return str(numerator)
    else:
        return f"{numerator}/{denominator}"
        
def create_fraction_table(n):
    """Create an n x n table of reduced fractions."""
    if n <= 0:
        return "Input must be a positive integer."
    
    # Create table data
    table_data = []
    for i in range(1, n+1):
        row = []
        for j in range(1, n+1):
            fraction = reduce_fraction(i, j)
            row.append(fraction)
        table_data.append(row)
    
    return table_data

# HTML template for the web page
HTML_TEMPLATE = '''
<!DOCTYPE html>
<html>
<head>
    <title>Bijection from the Natural Numbers to the Rational Numbers</title>
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
        .fraction-table-container {
            overflow-x: auto;
            max-width: 100%;
            margin-bottom: 20px;
        }
        .fraction-table {
            border-collapse: collapse;
            margin-top: 10px;
        }
        .fraction-table th, .fraction-table td {
            border: 1px solid #ddd;
            padding: 12px;
            text-align: center;
            min-width: 50px;
        }
        .fraction-table th {
            background-color: #f2f2f2;
            font-weight: bold;
            position: sticky;
            top: 0;
        }
        .diagonal-highlight {
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
        .new-entry {
            background-color: #e8f4fd;
            font-weight: bold;
        }
        .panel {
            flex: 1;
            min-width: 300px;
            margin-bottom: 20px;
        }
        .panel-title {
            margin-bottom: 10px;
            border-bottom: 1px solid #ddd;
            padding-bottom: 5px;
        }
    </style>
</head>
<body>
    <h1>Bijection from the Natural Numbers to the Rational Numbers</h1>
    <p>Enter a positive integer to generate a table of reduced fractions.</p>
    
    <form method="post">
        <label for="n">Enter a value between 5 and 25:</label>
        <input type="number" id="n" name="n" min="5" max="25" value="{{ n }}">
        <button type="submit">Generate Table</button>
    </form>
    
    {% if error %}
    <p class="error">{{ error }}</p>
    {% endif %}
    
    {% if table_data %}
    <div class="instructions">
        <p><strong>Interactive features:</strong></p>
        <p>Press <span class="key">Space</span> to move along an anti-diagonal zigzag pattern.</p>
        <p>The current cell value will appear in red in the table and be recorded in the history panel.</p>
        <p>For each new unique fraction, both its positive and negative values will be added to the bijection mapping.</p>
        <p class="position-info" id="positionInfo">Current position: (1,1)</p>
    </div>
    
    <div class="main-container">
        <!-- Left side: Fraction table -->
        <div class="panel">
            <h2 class="panel-title">{{ n }}x{{ n }} Fraction Table</h2>
            <div class="fraction-table-container">
                <table class="fraction-table" id="fractionTable">
                    <tr>
                        <th></th>
                        {% for j in range(1, n+1) %}
                            <th>{{ j }}</th>
                        {% endfor %}
                    </tr>
                    {% for i in range(n) %}
                        <tr>
                            <th>{{ i+1 }}</th>
                            {% for j in range(n) %}
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
                                    <th>Position</th>
                                    <th>Value</th>
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
                                    <th>ℚ</th>
                                </tr>
                            </thead>
                            <tbody id="bijectionBody">
                                <tr>
                                    <td>1</td>
                                    <td>0</td>
                                </tr>
                                <!-- Bijection entries will be added here -->
                            </tbody>
                        </table>
                    </div>
                </div>
            </div>
        </div>
    </div>

    <script>
        document.addEventListener('DOMContentLoaded', function() {
            const n = {{ n }};
            let step = 0;
            let history = [];
            let uniqueFractions = new Set(["0"]);  // Start with 0
            let bijectionCounter = 2;  // Start with 2 (1 is already used for 0)
            let lastHistoryRow = null;
            let lastBijectionRows = [];  // Keep track of the last rows added to the bijection table
            
            // Calculate all zigzag positions in advance
            const zigzagPositions = [];
            
            // Generate all anti-diagonal positions in zigzag order
            // We'll go through diagonals with sum of row+column from 2 to 2n
            for (let sum = 2; sum <= 2*n; sum++) {
                const positions = [];
                
                // For each sum, find all valid (row,col) pairs
                for (let row = 1; row <= n; row++) {
                    const col = sum - row;
                    if (col >= 1 && col <= n) {
                        positions.push([row, col]);
                    }
                }
                
                // If sum is odd, traverse from bottom to top
                // If sum is even, traverse from top to bottom
                if (sum % 2 !== 0) {
                    // For odd sums, reverse the positions
                    positions.reverse();
                }
                
                // Add all positions from this diagonal to our zigzag path
                zigzagPositions.push(...positions);
            }
            
            function updateHighlight() {
                // Clear all highlights
                for (let i = 1; i <= n; i++) {
                    for (let j = 1; j <= n; j++) {
                        const cell = document.getElementById(`cell-${i}-${j}`);
                        cell.classList.remove('diagonal-highlight');
                    }
                }
                
                // Remove highlighting from last entries
                if (lastHistoryRow) {
                    lastHistoryRow.classList.remove('new-entry');
                }
                
                lastBijectionRows.forEach(row => {
                    row.classList.remove('new-entry');
                });
                lastBijectionRows = [];
                
                // Current position in zigzag path
                const position = zigzagPositions[step];
                const row = position[0];
                const col = position[1];
                
                // Update position info display
                document.getElementById('positionInfo').textContent = `Current position: (${row},${col})`;
                
                // Highlight current cell
                const cell = document.getElementById(`cell-${row}-${col}`);
                cell.classList.add('diagonal-highlight');
                
                // Get the value of the current cell
                const value = cell.innerText;
                
                // Add to history
                history.push({
                    step: history.length + 1,
                    position: `(${row},${col})`,
                    value: value
                });
                
                // Update history table
                lastHistoryRow = updateHistoryTable();
                
                // Update bijection table if this is a new fraction
                if (!uniqueFractions.has(value) && value !== "0") {
                    uniqueFractions.add(value);
                    
                    // Add positive value
                    const posRow = updateBijectionTable(value);
                    lastBijectionRows.push(posRow);
                    
                    // Add negative value
                    const negValue = value.startsWith("-") ? value.substring(1) : "-" + value;
                    uniqueFractions.add(negValue);
                    const negRow = updateBijectionTable(negValue);
                    lastBijectionRows.push(negRow);
                }
            }
            
            function updateHistoryTable() {
                const historyBody = document.getElementById('historyBody');
                
                // Get the latest history entry
                const entry = history[history.length - 1];
                
                // Create new row with the new-entry class
                const row = document.createElement('tr');
                row.classList.add('new-entry');
                
                row.innerHTML = `
                    <td>${entry.step}</td>
                    <td>${entry.position}</td>
                    <td>${entry.value}</td>
                `;
                
                historyBody.appendChild(row);
                
                // Scroll to the bottom of history container
                const historyContainer = document.querySelector('.history-container');
                historyContainer.scrollTop = historyContainer.scrollHeight;
                
                return row;
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
            
            function movePosition() {
                // Move to next position in zigzag pattern
                step = (step + 1) % zigzagPositions.length;
                updateHighlight();
            }
            
            // Initialize the first highlight and history
            updateHighlight();
            
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
    n = 5  # Default value
    
    if request.method == 'POST':
        try:
            n = int(request.form.get('n', 5))
            if n < 5:
                error = "Please enter a value of at least 5 for better visualization."
            elif n > 25:
                error = "Please use a value of 25 or less to ensure the table displays correctly."
            else:
                table_data = create_fraction_table(n)
        except ValueError:
            error = "Invalid input. Please enter a positive integer."
    else:
        # For GET requests, generate the default table
        table_data = create_fraction_table(n)
    
    return render_template_string(HTML_TEMPLATE, table_data=table_data, error=error, n=n)

if __name__ == '__main__':
    app.run(debug=True)
