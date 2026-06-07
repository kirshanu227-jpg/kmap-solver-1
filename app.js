// app.js

// Term class representing a product term or sum term
class Term {
    constructor(str, covered) {
        this.str = str; // e.g. "1-0-"
        this.covered = new Set(covered); // array of original minterms covered
        this.used = false; // flag for Quine-McCluskey grouping
    }
}

// ----------------------------------------------------
// CORE SOLVER: QUINE-MCCLUSKEY ALGORITHM
// ----------------------------------------------------

// Combines two binary strings if they differ by exactly one bit (e.g. "001" and "011" -> "0-1")
function combineStrings(s1, s2) {
    let diffIndex = -1;
    let diffs = 0;
    for (let i = 0; i < s1.length; i++) {
        if (s1[i] !== s2[i]) {
            diffs++;
            diffIndex = i;
        }
    }
    if (diffs === 1 && ((s1[diffIndex] === '0' && s2[diffIndex] === '1') || (s1[diffIndex] === '1' && s2[diffIndex] === '0'))) {
        return s1.substring(0, diffIndex) + '-' + s1.substring(diffIndex + 1);
    }
    return null;
}

// Finds all Prime Implicants using the Quine-McCluskey method
function findPrimeImplicants(minterms, dontCares, numVars) {
    let currentTerms = [];
    
    // Create initial terms for minterms
    for (const m of minterms) {
        const bin = m.toString(2).padStart(numVars, '0');
        currentTerms.push(new Term(bin, [m]));
    }
    
    // Create initial terms for don't cares (cover no original minterms)
    for (const d of dontCares) {
        const bin = d.toString(2).padStart(numVars, '0');
        currentTerms.push(new Term(bin, []));
    }
    
    let primeImplicants = [];
    
    // Iteratively combine terms
    while (currentTerms.length > 0) {
        const nextTerms = [];
        
        for (let i = 0; i < currentTerms.length; i++) {
            for (let j = i + 1; j < currentTerms.length; j++) {
                const t1 = currentTerms[i];
                const t2 = currentTerms[j];
                
                const combinedStr = combineStrings(t1.str, t2.str);
                if (combinedStr !== null) {
                    t1.used = true;
                    t2.used = true;
                    
                    const unionCovered = new Set([...t1.covered, ...t2.covered]);
                    const newTerm = new Term(combinedStr, Array.from(unionCovered));
                    
                    // Prevent duplicate terms in the next level
                    if (!nextTerms.some(nt => nt.str === newTerm.str)) {
                        nextTerms.push(newTerm);
                    }
                }
            }
        }
        
        // Uncombined terms are Prime Implicants
        for (const t of currentTerms) {
            if (!t.used) {
                // Only keep prime implicants that cover at least one original minterm
                if (t.covered.size > 0) {
                    primeImplicants.push(t);
                }
            }
        }
        
        currentTerms = nextTerms;
    }
    
    // Deduplicate PIs (redundancy check)
    const uniquePIs = [];
    for (const pi of primeImplicants) {
        if (!uniquePIs.some(u => u.str === pi.str)) {
            uniquePIs.push(pi);
        }
    }
    
    return uniquePIs;
}

// Solves the Prime Implicant chart using Essential PIs and Backtracking Search
function getMinimalCover(primeImplicants, minterms) {
    if (minterms.length === 0) return [];
    
    // Map minterms to the Prime Implicants that cover them
    const mintermToPIs = {};
    for (const m of minterms) {
        mintermToPIs[m] = [];
    }
    for (const pi of primeImplicants) {
        for (const m of pi.covered) {
            if (minterms.includes(m)) {
                mintermToPIs[m].push(pi);
            }
        }
    }
    
    // Identify Essential Prime Implicants (EPIs)
    const essentialPIs = new Set();
    for (const m of minterms) {
        if (mintermToPIs[m].length === 1) {
            essentialPIs.add(mintermToPIs[m][0]);
        }
    }
    
    // Calculate what minterms are already covered by Essential PIs
    const coveredByEssential = new Set();
    for (const epi of essentialPIs) {
        for (const m of epi.covered) {
            coveredByEssential.add(m);
        }
    }
    
    // Find minterms that still need to be covered
    const remainingMinterms = minterms.filter(m => !coveredByEssential.has(m));
    const remainingPIs = primeImplicants.filter(pi => !essentialPIs.has(pi));
    
    if (remainingMinterms.length === 0) {
        return Array.from(essentialPIs);
    }
    
    // Backtracking Search to find exact minimal cover of remaining minterms
    let bestCover = null;
    let bestCoverLiteralCount = Infinity;
    
    function getLiteralCount(cover) {
        let count = 0;
        for (const pi of cover) {
            for (const c of pi.str) {
                if (c !== '-') count++;
            }
        }
        return count;
    }
    
    function search(index, currentCover, currentlyCovered) {
        // Check if all remaining minterms are covered
        const allCovered = remainingMinterms.every(m => currentlyCovered.has(m));
        if (allCovered) {
            const fullCover = [...Array.from(essentialPIs), ...currentCover];
            const litCount = getLiteralCount(fullCover);
            
            if (bestCover === null || 
                fullCover.length < bestCover.length || 
                (fullCover.length === bestCover.length && litCount < bestCoverLiteralCount)) {
                bestCover = fullCover;
                bestCoverLiteralCount = litCount;
            }
            return;
        }
        
        // Pruning checks
        if (index >= remainingPIs.length) return;
        if (bestCover !== null && currentCover.length >= bestCover.length - essentialPIs.size) return;
        
        // Path 1: Include remainingPIs[index] (only if it covers any remaining uncovered minterms)
        const pi = remainingPIs[index];
        const nextCovered = new Set(currentlyCovered);
        let addedAny = false;
        
        for (const m of pi.covered) {
            if (remainingMinterms.includes(m) && !nextCovered.has(m)) {
                nextCovered.add(m);
                addedAny = true;
            }
        }
        
        if (addedAny) {
            currentCover.push(pi);
            search(index + 1, currentCover, nextCovered);
            currentCover.pop();
        }
        
        // Path 2: Exclude remainingPIs[index]
        search(index + 1, currentCover, currentlyCovered);
    }
    
    search(0, [], new Set());
    
    if (bestCover === null) {
        return [...Array.from(essentialPIs), ...remainingPIs];
    }
    
    return bestCover;
}

// Helper to solve expressions for either SOP or POS
function solveKMap(minterms, dontCares, numVars, isPOS = false) {
    const PIs = findPrimeImplicants(minterms, dontCares, numVars);
    const cover = getMinimalCover(PIs, minterms);
    return cover;
}

// ----------------------------------------------------
// FORMATTERS FOR BOOLEAN EXPRESSIONS
// ----------------------------------------------------

const VARS = ['A', 'B', 'C', 'D'];

function formatSOP(terms, numVars) {
    if (terms.length === 0) return "0";
    if (terms.length === 1 && terms[0].str.split('').every(c => c === '-')) return "1";
    
    const formatted = terms.map(t => {
        let termStr = "";
        for (let i = 0; i < t.str.length; i++) {
            if (t.str[i] === '1') {
                termStr += VARS[i];
            } else if (t.str[i] === '0') {
                termStr += VARS[i] + "'";
            }
        }
        return termStr || "1";
    });
    
    return formatted.join(' + ');
}

function formatPOS(terms, numVars) {
    if (terms.length === 0) return "1";
    if (terms.length === 1 && terms[0].str.split('').every(c => c === '-')) return "0";
    
    const formatted = terms.map(t => {
        let sumParts = [];
        for (let i = 0; i < t.str.length; i++) {
            if (t.str[i] === '0') {
                sumParts.push(VARS[i]);
            } else if (t.str[i] === '1') {
                sumParts.push(VARS[i] + "'");
            }
        }
        if (sumParts.length === 0) return "";
        return sumParts.length === 1 ? sumParts[0] : `(${sumParts.join(' + ')})`;
    }).filter(s => s !== "");
    
    if (formatted.length === 1) {
        // strip parentheses if only one sum term
        const t = formatted[0];
        return t.startsWith('(') && t.endsWith(')') ? t.substring(1, t.length - 1) : t;
    }
    
    // If they were single items, wrap them back for multiplication
    return formatted.map(t => t.startsWith('(') ? t : `(${t})`).join('');
}

// ----------------------------------------------------
// CYCLIC RANGE BOUNDARY CALCULATIONS (FOR VISUALIZATION)
// ----------------------------------------------------

// Finds the contiguous range (possibly cyclic wrapping) in an array
function getCyclicRange(indices, size) {
    if (indices.length === 0) return null;
    const set = new Set(indices);
    const span = indices.length;
    
    for (let start = 0; start < size; start++) {
        let match = true;
        for (let i = 0; i < span; i++) {
            if (!set.has((start + i) % size)) {
                match = false;
                break;
            }
        }
        if (match) {
            return { start, span };
        }
    }
    return null;
}

// Decomposes a cyclic range into standard rectangular bounds [min, max]
function getIntervals(start, span, size) {
    if (start + span <= size) {
        return [{ min: start, max: start + span - 1 }];
    } else {
        return [
            { min: start, max: size - 1 },
            { min: 0, max: (start + span - 1) % size }
        ];
    }
}

// Maps a 1D cell index to 2D Gray-coded grid coordinates (r, c)
function getGridCoords(idx, numVars) {
    if (numVars === 4) {
        const a = (idx >> 3) & 1;
        const b = (idx >> 2) & 1;
        const c = (idx >> 1) & 1;
        const d = idx & 1;
        const ab = (a << 1) | b;
        const cd = (c << 1) | d;
        const rMap = { 0: 0, 1: 1, 3: 2, 2: 3 };
        const cMap = { 0: 0, 1: 1, 3: 2, 2: 3 };
        return { r: rMap[ab], c: cMap[cd] };
    } else if (numVars === 3) {
        const a = (idx >> 2) & 1;
        const b = (idx >> 1) & 1;
        const c = idx & 1;
        const bc = (b << 1) | c;
        const cMap = { 0: 0, 1: 1, 3: 2, 2: 3 };
        return { r: a, c: cMap[bc] };
    } else { // 2 variables
        const a = (idx >> 1) & 1;
        const b = idx & 1;
        return { r: a, c: b };
    }
}

// Predefined vibrant HSL hues for group coverings
const GROUP_HUES = [
    215, // Bright Blue
    145, // Emerald Green
    275, // Violet Purple
    30,  // Amber Orange
    345, // Rose Pink
    175, // Sea Teal
    55,  // Gold Yellow
    0    // Coral Red
];

// ----------------------------------------------------
// STATE & APP LIFE CYCLE
// ----------------------------------------------------

let state = {
    numVars: 4,
    cellValues: Array(16).fill('0'), // '0', '1', or 'X'
    sopCover: [],
    posCover: []
};

// Initializes elements
const selectVarsEl = document.getElementById('select-vars');
const kmapGridEl = document.getElementById('kmap-grid-container');
const sopExpressionEl = document.getElementById('sop-expression');
const posExpressionEl = document.getElementById('pos-expression');
const sopLegendEl = document.getElementById('sop-legend');
const posLegendEl = document.getElementById('pos-legend');
const truthTableHeaderEl = document.getElementById('truth-table-header');
const truthTableBodyEl = document.getElementById('truth-table-body');
const btnResetEl = document.getElementById('btn-reset');
const btnPrintEl = document.getElementById('btn-print');
const groupingExplanationEl = document.getElementById('grouping-explanation');

// Navigation Tabs
document.querySelectorAll('.nav-tab').forEach(tab => {
    tab.addEventListener('click', () => {
        document.querySelectorAll('.nav-tab').forEach(t => t.classList.remove('active'));
        document.querySelectorAll('.tab-panel').forEach(p => p.classList.remove('active'));
        
        tab.classList.add('active');
        const contentId = `tab-content-${tab.dataset.tab}`;
        document.getElementById(contentId).classList.add('active');
    });
});

// Load Corners Example on Learn Tab
const btnLoadCornersExample = document.getElementById('btn-load-corners-example');
if (btnLoadCornersExample) {
    btnLoadCornersExample.addEventListener('click', () => {
        // Switch to solver tab
        document.querySelector('.nav-tab[data-tab="solver"]').click();
        loadExample('corners-4');
    });
}

// Reset Map Values
btnResetEl.addEventListener('click', () => {
    state.cellValues.fill('0');
    updateApp();
});

// Export Lab Report (PDF via system Print)
btnPrintEl.addEventListener('click', () => {
    window.print();
});

// Handle Variable Count Changes
selectVarsEl.addEventListener('click', (e) => {
    // Avoid double trigger if click is just selecting, but e.target change is correct
});
selectVarsEl.addEventListener('change', (e) => {
    const newCount = parseInt(e.target.value);
    state.numVars = newCount;
    state.cellValues = Array(Math.pow(2, newCount)).fill('0');
    updateApp();
});

// Setup example buttons listeners
document.querySelectorAll('.example-buttons button').forEach(btn => {
    btn.addEventListener('click', () => {
        loadExample(btn.dataset.example);
    });
});

const EXAMPLES = {
    'xor-3': {
        vars: 3,
        minterms: [1, 2, 4, 7],
        dontCares: []
    },
    'majority-3': {
        vars: 3,
        minterms: [3, 5, 6, 7],
        dontCares: []
    },
    'corners-4': {
        vars: 4,
        minterms: [0, 2, 8, 10],
        dontCares: []
    },
    'mux-4': {
        vars: 4,
        minterms: [10, 11, 13, 15],
        dontCares: []
    },
    'bcd-invalid': {
        vars: 4,
        minterms: [1, 3, 5, 7, 9],
        dontCares: [10, 11, 12, 13, 14, 15]
    }
};

function loadExample(key) {
    const ex = EXAMPLES[key];
    if (!ex) return;
    
    state.numVars = ex.vars;
    selectVarsEl.value = ex.vars.toString();
    state.cellValues = Array(Math.pow(2, ex.vars)).fill('0');
    
    for (const m of ex.minterms) {
        state.cellValues[m] = '1';
    }
    for (const d of ex.dontCares) {
        state.cellValues[d] = 'X';
    }
    
    updateApp();
}

// ----------------------------------------------------
// VIEW RENDERING ENGINE
// ----------------------------------------------------

function updateApp() {
    // 1. Set sizing variables on CSS grid
    const numRows = state.numVars === 4 ? 4 : 2;
    const numCols = state.numVars === 2 ? 2 : 4;
    kmapGridEl.style.setProperty('--kmap-rows', numRows.toString());
    kmapGridEl.style.setProperty('--kmap-cols', numCols.toString());
    
    // 2. Resolve Minterms and Don't Cares lists
    const minterms = [];
    const dontCares = [];
    const maxterms = []; // cells containing '0'
    
    for (let i = 0; i < state.cellValues.length; i++) {
        if (state.cellValues[i] === '1') {
            minterms.push(i);
        } else if (state.cellValues[i] === 'X') {
            dontCares.push(i);
        } else {
            maxterms.push(i);
        }
    }
    
    // 3. Solve for SOP and POS Covers
    state.sopCover = solveKMap(minterms, dontCares, state.numVars, false);
    state.posCover = solveKMap(maxterms, dontCares, state.numVars, true);
    
    // 4. Render Grid DOM
    renderKMapGrid(numRows, numCols);
    
    // 5. Render Minimized Expressions
    renderExpressions();
    
    // 6. Draw Highlight Groups Overlay
    drawOverlays(numRows, numCols);
    
    // 7. Update Truth Table
    renderTruthTable();
}

// Renders the K-Map Grid structure (headers and cells)
function renderKMapGrid(numRows, numCols) {
    kmapGridEl.innerHTML = "";
    
    // 1. Diagonal header separator cell
    const diagCell = document.createElement('div');
    diagCell.className = "kmap-diagonal-cell";
    
    // SVG Diagonal line
    diagCell.innerHTML = `
        <svg class="kmap-diagonal-line" width="100%" height="100%">
            <line x1="0" y1="0" x2="100%" y2="100%"></line>
        </svg>
        <span class="kmap-label-row-var">${state.numVars === 4 ? 'AB' : 'A'}</span>
        <span class="kmap-label-col-var">${state.numVars === 4 ? 'CD' : (state.numVars === 3 ? 'BC' : 'B')}</span>
    `;
    kmapGridEl.appendChild(diagCell);
    
    // 2. Top column headers labeled in Gray Code
    const colLabels = numCols === 4 ? ['00', '01', '11', '10'] : ['0', '1'];
    for (let c = 0; c < numCols; c++) {
        const colHeader = document.createElement('div');
        colHeader.className = "kmap-header-cell kmap-header-col";
        colHeader.innerText = colLabels[c];
        kmapGridEl.appendChild(colHeader);
    }
    
    // 3. Rows: Row Header + Row Cells
    const rowLabels = numRows === 4 ? ['00', '01', '11', '10'] : ['0', '1'];
    const rMap = numRows === 4 ? { 0: 0, 1: 1, 2: 3, 3: 2 } : { 0: 0, 1: 1 };
    const cMap = numCols === 4 ? { 0: 0, 1: 1, 2: 3, 3: 2 } : { 0: 0, 1: 1 };
    
    for (let r = 0; r < numRows; r++) {
        // Row Label
        const rowHeader = document.createElement('div');
        rowHeader.className = "kmap-header-cell kmap-header-row";
        rowHeader.innerText = rowLabels[r];
        kmapGridEl.appendChild(rowHeader);
        
        // Interactive cells
        for (let c = 0; c < numCols; c++) {
            // Find cell index from grid row and column index
            // Map row & col index back to their Gray-code values (ab, cd)
            const rVal = rMap[r];
            const cVal = cMap[c];
            let cellIndex = 0;
            
            if (state.numVars === 4) {
                cellIndex = (rVal << 2) | cVal;
            } else if (state.numVars === 3) {
                cellIndex = (rVal << 2) | cVal;
            } else {
                cellIndex = (rVal << 1) | cVal;
            }
            
            const cellValue = state.cellValues[cellIndex];
            
            const cellEl = document.createElement('div');
            cellEl.className = "kmap-cell";
            cellEl.dataset.index = cellIndex.toString();
            
            let valClass = "cell-0";
            if (cellValue === '1') valClass = "cell-1";
            if (cellValue === 'X') valClass = "cell-x";
            
            cellEl.innerHTML = `
                <span class="cell-value ${valClass}">${cellValue}</span>
                <span class="cell-index">${cellIndex}</span>
            `;
            
            // Interaction: cycle cell values on click
            cellEl.addEventListener('click', () => {
                let current = state.cellValues[cellIndex];
                let next = '0';
                if (current === '0') next = '1';
                else if (current === '1') next = 'X';
                
                state.cellValues[cellIndex] = next;
                updateApp();
                
                // Flash scale animation on value click
                const valEl = cellEl.querySelector('.cell-value');
                valEl.style.transform = 'scale(1.25)';
                setTimeout(() => {
                    valEl.style.transform = 'scale(1)';
                }, 100);
            });
            
            kmapGridEl.appendChild(cellEl);
        }
    }
}

// Renders the SOP and POS minimized equations and legends
function renderExpressions() {
    // 1. SOP
    const sopText = formatSOP(state.sopCover, state.numVars);
    sopExpressionEl.innerHTML = `F = ${sopText}`;
    
    // SOP Legend Badges
    sopLegendEl.innerHTML = "";
    if (state.sopCover.length > 0 && !(state.sopCover.length === 1 && state.sopCover[0].str.split('').every(c => c === '-'))) {
        state.sopCover.forEach((term, index) => {
            const hue = GROUP_HUES[index % GROUP_HUES.length];
            const termText = formatSOP([term], state.numVars);
            
            const badge = document.createElement('div');
            badge.className = `legend-term group-badge-${index}`;
            badge.style.borderColor = `hsl(${hue}, 80%, 45%)`;
            badge.style.backgroundColor = `hsla(${hue}, 80%, 50%, 0.08)`;
            badge.style.color = `hsl(${hue}, 90%, 30%)`;
            badge.innerHTML = `
                <span class="color-dot" style="background-color: hsl(${hue}, 80%, 45%);"></span>
                <span>${termText}</span>
            `;
            
            // Hover interaction to glow corresponding K-Map groups
            badge.addEventListener('mouseenter', () => {
                document.querySelectorAll(`.kmap-overlay-group-${index}`).forEach(el => {
                    el.classList.add('hovered');
                    el.style.boxShadow = `0 0 16px hsl(${hue}, 80%, 45%)`;
                    el.style.backgroundColor = `hsla(${hue}, 80%, 50%, 0.25)`;
                });
            });
            badge.addEventListener('mouseleave', () => {
                document.querySelectorAll(`.kmap-overlay-group-${index}`).forEach(el => {
                    el.classList.remove('hovered');
                    el.style.boxShadow = 'none';
                    el.style.backgroundColor = `hsla(${hue}, 80%, 50%, 0.15)`;
                });
            });
            
            sopLegendEl.appendChild(badge);
        });
    }
    
    // 2. POS
    const posText = formatPOS(state.posCover, state.numVars);
    posExpressionEl.innerHTML = `F = ${posText}`;
    
    // POS Legend Badges
    posLegendEl.innerHTML = "";
    if (state.posCover.length > 0 && !(state.posCover.length === 1 && state.posCover[0].str.split('').every(c => c === '-'))) {
        state.posCover.forEach((term, index) => {
            // Use slightly offset hues or same hues for POS
            const hue = GROUP_HUES[(index + 3) % GROUP_HUES.length];
            const termText = formatPOS([term], state.numVars);
            
            const badge = document.createElement('div');
            badge.className = `legend-term pos-badge-${index}`;
            badge.style.borderColor = `hsl(${hue}, 75%, 45%)`;
            badge.style.backgroundColor = `hsla(${hue}, 75%, 50%, 0.08)`;
            badge.style.color = `hsl(${hue}, 85%, 30%)`;
            badge.innerHTML = `
                <span class="color-dot" style="background-color: hsl(${hue}, 75%, 45%);"></span>
                <span>${termText}</span>
            `;
            
            // Hover highlights the POS cells (since POS groups are 0s, we don't draw overlapping overlays for POS and SOP at the same time to avoid visual clutter, but we can highlight the grid cells directly! This is an amazing double-detail!)
            badge.addEventListener('mouseenter', () => {
                term.covered.forEach(m => {
                    const cell = kmapGridEl.querySelector(`.kmap-cell[data-index="${m}"]`);
                    if (cell) {
                        cell.style.backgroundColor = `hsla(${hue}, 75%, 50%, 0.2)`;
                        cell.style.borderColor = `hsl(${hue}, 75%, 45%)`;
                        cell.style.boxShadow = `inset 0 0 8px hsla(${hue}, 75%, 45%, 0.3)`;
                    }
                });
            });
            badge.addEventListener('mouseleave', () => {
                term.covered.forEach(m => {
                    const cell = kmapGridEl.querySelector(`.kmap-cell[data-index="${m}"]`);
                    if (cell) {
                        cell.style.backgroundColor = "";
                        cell.style.borderColor = "";
                        cell.style.boxShadow = "";
                    }
                });
            });
            
            posLegendEl.appendChild(badge);
        });
    }
    
    // 3. Step-by-Step Explanation
    if (groupingExplanationEl) {
        let explanationHTML = "";

        // SOP Explanation
        explanationHTML += `<h4 style="font-size: 0.85rem; text-transform: uppercase; letter-spacing: 0.05em; color: var(--text-muted); margin-bottom: 0.5rem; margin-top: 0.5rem;">SOP Grouping Details</h4>`;
        if (state.sopCover.length === 0) {
            explanationHTML += `<p style="margin-bottom: 1rem; color: var(--text-muted);">No minterms are active. The expression simplifies to <code>F = 0</code>.</p>`;
        } else if (state.sopCover.length === 1 && state.sopCover[0].str.split('').every(c => c === '-')) {
            explanationHTML += `<p style="margin-bottom: 1rem; color: var(--text-muted);">All cells are active (1 or X). The expression simplifies to <code>F = 1</code>.</p>`;
        } else {
            state.sopCover.forEach((term, index) => {
                explanationHTML += explainSOPTerm(term, index, state.numVars);
            });
        }

        // POS Explanation
        explanationHTML += `<h4 style="font-size: 0.85rem; text-transform: uppercase; letter-spacing: 0.05em; color: var(--text-muted); margin-bottom: 0.5rem; margin-top: 1rem;">POS Grouping Details</h4>`;
        if (state.posCover.length === 0) {
            explanationHTML += `<p style="color: var(--text-muted);">All cells are active (1 or X). The POS expression simplifies to <code>F = 1</code>.</p>`;
        } else if (state.posCover.length === 1 && state.posCover[0].str.split('').every(c => c === '-')) {
            explanationHTML += `<p style="color: var(--text-muted);">No cells are active (all cells are 0 or X). The POS expression simplifies to <code>F = 0</code>.</p>`;
        } else {
            state.posCover.forEach((term, index) => {
                explanationHTML += explainPOSTerm(term, index, state.numVars);
            });
        }

        groupingExplanationEl.innerHTML = explanationHTML;
    }
}

// SOP/POS Explanation helpers
function explainSOPTerm(term, index, numVars) {
    const cells = Array.from(term.covered);
    cells.sort((a, b) => a - b);
    const hue = GROUP_HUES[index % GROUP_HUES.length];
    
    let html = `<div style="margin-bottom: 0.75rem; border-left: 3px solid hsl(${hue}, 80%, 45%); padding-left: 0.5rem;">`;
    html += `<strong>Group ${index + 1}</strong> (Covers cells: {${cells.join(', ')}}):<br>`;
    
    let constantParts = [];
    let variableExplanation = [];
    for (let i = 0; i < numVars; i++) {
        if (term.str[i] === '1') {
            constantParts.push(VARS[i]);
            variableExplanation.push(`${VARS[i]} is constant at 1 (${VARS[i]})`);
        } else if (term.str[i] === '0') {
            constantParts.push(VARS[i] + "'");
            variableExplanation.push(`${VARS[i]} is constant at 0 (${VARS[i]}')`);
        } else {
            variableExplanation.push(`${VARS[i]} varies (eliminated)`);
        }
    }
    
    html += `<span style="font-size: 0.8rem; color: var(--text-muted);">${variableExplanation.join(', ')}</span><br>`;
    html += `Term contribution: <code style="font-weight: 600; color: hsl(${hue}, 90%, 30%); font-family: var(--font-mono);">${constantParts.join('') || '1'}</code>`;
    html += `</div>`;
    return html;
}

function explainPOSTerm(term, index, numVars) {
    const cells = Array.from(term.covered);
    cells.sort((a, b) => a - b);
    const hue = GROUP_HUES[(index + 3) % GROUP_HUES.length];
    
    let html = `<div style="margin-bottom: 0.75rem; border-left: 3px solid hsl(${hue}, 75%, 45%); padding-left: 0.5rem;">`;
    html += `<strong>Group ${index + 1}</strong> (Covers 0-cells: {${cells.join(', ')}}):<br>`;
    
    let sumParts = [];
    let variableExplanation = [];
    for (let i = 0; i < numVars; i++) {
        if (term.str[i] === '0') {
            sumParts.push(VARS[i]);
            variableExplanation.push(`${VARS[i]} is constant at 0 (${VARS[i]})`);
        } else if (term.str[i] === '1') {
            sumParts.push(VARS[i] + "'");
            variableExplanation.push(`${VARS[i]} is constant at 1 (${VARS[i]}')`);
        } else {
            variableExplanation.push(`${VARS[i]} varies (eliminated)`);
        }
    }
    
    html += `<span style="font-size: 0.8rem; color: var(--text-muted);">${variableExplanation.join(', ')}</span><br>`;
    const sumTermText = sumParts.length === 1 ? sumParts[0] : `(${sumParts.join(' + ')})`;
    html += `Term contribution: <code style="font-weight: 600; color: hsl(${hue}, 85%, 30%); font-family: var(--font-mono);">${sumTermText}</code>`;
    html += `</div>`;
    return html;
}

// Draws the visual highlighting overlays on top of the K-map grid for SOP groups
function drawOverlays(numRows, numCols) {
    // Remove all old overlay divs
    document.querySelectorAll('.kmap-group-overlay').forEach(el => el.remove());
    
    // We only display overlays for SOP groupings (the 1s and Xs combined)
    // If the cover represents "1" (all cells), we draw a single overlay covering the entire cell region
    if (state.sopCover.length === 1 && state.sopCover[0].str.split('').every(c => c === '-')) {
        const fullOverlay = document.createElement('div');
        fullOverlay.className = "kmap-group-overlay kmap-overlay-group-0";
        fullOverlay.style.gridRow = `2 / ${numRows + 2}`;
        fullOverlay.style.gridColumn = `2 / ${numCols + 2}`;
        
        const hue = GROUP_HUES[0];
        fullOverlay.style.backgroundColor = `hsla(${hue}, 80%, 50%, 0.15)`;
        fullOverlay.style.borderColor = `hsl(${hue}, 80%, 45%)`;
        fullOverlay.style.borderStyle = 'solid';
        fullOverlay.style.borderWidth = '2px';
        fullOverlay.style.borderRadius = '10px';
        
        kmapGridEl.appendChild(fullOverlay);
        return;
    }
    
    state.sopCover.forEach((term, index) => {
        // If this term doesn't cover anything, skip
        if (term.covered.size === 0) return;
        
        // Find grid coordinates of all covered cells
        const coords = Array.from(term.covered).map(idx => getGridCoords(idx, state.numVars));
        
        // Extract row and column indexes in Gray Code grid coordinates
        const rows = Array.from(new Set(coords.map(co => co.r)));
        const cols = Array.from(new Set(coords.map(co => co.c)));
        
        // Compute cyclic ranges
        const rowRange = getCyclicRange(rows, numRows);
        const colRange = getCyclicRange(cols, numCols);
        
        if (!rowRange || !colRange) return;
        
        // Decompose ranges to rectangular boundaries
        const rowIntervals = getIntervals(rowRange.start, rowRange.span, numRows);
        const colIntervals = getIntervals(colRange.start, colRange.span, numCols);
        
        const hue = GROUP_HUES[index % GROUP_HUES.length];
        
        // Check if there is cyclic wrapping
        const colsWrap = colRange.start + colRange.span > numCols;
        const rowsWrap = rowRange.start + rowRange.span > numRows;
        
        // Cross-product of row intervals and column intervals yields rectangles
        for (const rInv of rowIntervals) {
            for (const cInv of colIntervals) {
                const overlay = document.createElement('div');
                overlay.className = `kmap-group-overlay kmap-overlay-group-${index}`;
                
                // CSS Grid lines placement
                // Cell index 0 corresponds to grid row 2, grid col 2
                overlay.style.gridRow = `${rInv.min + 2} / ${rInv.max + 3}`;
                overlay.style.gridColumn = `${cInv.min + 2} / ${cInv.max + 3}`;
                
                // Color formatting
                overlay.style.backgroundColor = `hsla(${hue}, 80%, 50%, 0.12)`;
                overlay.style.borderColor = `hsl(${hue}, 80%, 45%)`;
                overlay.style.borderStyle = 'solid';
                overlay.style.borderWidth = '2px';
                overlay.style.borderRadius = '10px';
                
                // Polish borders dynamically for wrapping groups!
                if (colsWrap) {
                    if (cInv.max === numCols - 1) { // Left half of split
                        overlay.style.borderRightWidth = '0';
                        overlay.style.borderTopRightRadius = '0';
                        overlay.style.borderBottomRightRadius = '0';
                    }
                    if (cInv.min === 0) { // Right half of split
                        overlay.style.borderLeftWidth = '0';
                        overlay.style.borderTopLeftRadius = '0';
                        overlay.style.borderBottomLeftRadius = '0';
                    }
                }
                
                if (rowsWrap) {
                    if (rInv.max === numRows - 1) { // Top half of split
                        overlay.style.borderBottomWidth = '0';
                        overlay.style.borderBottomLeftRadius = '0';
                        overlay.style.borderBottomRightRadius = '0';
                    }
                    if (rInv.min === 0) { // Bottom half of split
                        overlay.style.borderTopWidth = '0';
                        overlay.style.borderTopLeftRadius = '0';
                        overlay.style.borderTopRightRadius = '0';
                    }
                }
                
                kmapGridEl.appendChild(overlay);
            }
        }
    });
}

// Renders the truth table dynamically
function renderTruthTable() {
    // 1. Generate Header columns based on number of variables
    truthTableHeaderEl.innerHTML = "";
    for (let i = 0; i < state.numVars; i++) {
        const th = document.createElement('th');
        th.innerText = VARS[i];
        truthTableHeaderEl.appendChild(th);
    }
    const thOut = document.createElement('th');
    thOut.className = "col-out";
    thOut.innerText = "F";
    truthTableHeaderEl.appendChild(thOut);
    
    // 2. Generate Rows
    truthTableBodyEl.innerHTML = "";
    const size = Math.pow(2, state.numVars);
    for (let idx = 0; idx < size; idx++) {
        const tr = document.createElement('tr');
        
        // Highlight active minterms in table
        const cellValue = state.cellValues[idx];
        if (cellValue === '1') {
            tr.className = "active-row";
        }
        
        // Input bits
        for (let i = state.numVars - 1; i >= 0; i--) {
            const bit = (idx >> i) & 1;
            const td = document.createElement('td');
            td.innerText = bit.toString();
            tr.appendChild(td);
        }
        
        // Output column
        const tdOut = document.createElement('td');
        tdOut.className = "col-out";
        tdOut.innerText = cellValue;
        
        // Make the output value styled
        if (cellValue === '1') {
            tdOut.style.color = "var(--primary-color)";
        } else if (cellValue === 'X') {
            tdOut.style.color = "hsl(25, 85%, 45%)";
        }
        
        tr.appendChild(tdOut);
        
        // Hovering over truth table row highlights corresponding cell in K-Map Grid!
        tr.addEventListener('mouseenter', () => {
            const cell = kmapGridEl.querySelector(`.kmap-cell[data-index="${idx}"]`);
            if (cell) {
                cell.style.backgroundColor = "var(--accent-light)";
                cell.style.borderColor = "var(--accent-color)";
            }
        });
        tr.addEventListener('mouseleave', () => {
            const cell = kmapGridEl.querySelector(`.kmap-cell[data-index="${idx}"]`);
            if (cell) {
                cell.style.backgroundColor = "";
                cell.style.borderColor = "";
            }
        });
        
        truthTableBodyEl.appendChild(tr);
    }
}

// Setup Copy Buttons Clipboard Handlers
function setupClipboardCopy(buttonId, valueSourceEl) {
    const btn = document.getElementById(buttonId);
    btn.addEventListener('click', () => {
        const rawText = valueSourceEl.innerText.replace('F = ', '');
        navigator.clipboard.writeText(rawText).then(() => {
            // Visual feedback: change copy icon to checked SVG
            const originalHTML = btn.innerHTML;
            btn.innerHTML = `
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round" style="color: var(--accent-color);"><polyline points="20 6 9 17 4 12"></polyline></svg>
            `;
            
            // Show toast message
            showToast(`Copied: ${rawText}`, 'success');
            
            setTimeout(() => {
                btn.innerHTML = originalHTML;
            }, 1500);
        }).catch(err => {
            showToast('Failed to copy to clipboard', 'error');
        });
    });
}

setupClipboardCopy('btn-copy-sop', sopExpressionEl);
setupClipboardCopy('btn-copy-pos', posExpressionEl);

// Toast system for messages
const toastEl = document.getElementById('test-toast-el');
const toastTextEl = document.getElementById('test-toast-text');

function showToast(message, type = 'info') {
    toastEl.className = `test-toast ${type} show`;
    toastTextEl.innerText = message;
    
    // Auto hide after 3 seconds
    setTimeout(() => {
        toastEl.classList.remove('show');
    }, 3000);
}

// ----------------------------------------------------
// SYSTEM DIAGNOSTICS & SELF-TEST SUITE
// ----------------------------------------------------

function runDiagnostics() {
    console.log("Running Karnaugh Map Solver Diagnostics...");
    let passed = true;
    
    // Test Case 1: 2-Var XOR (F = Sum(1, 2))
    const tc1 = solveKMap([1, 2], [], 2);
    const tc1Str = formatSOP(tc1, 2);
    // Expect: A'B + AB' (order could be A'B + AB' or AB' + A'B)
    const tc1Valid = tc1Str === "A'B + AB'" || tc1Str === "AB' + A'B";
    if (!tc1Valid) {
        console.error("Test Case 1 failed. Got:", tc1Str);
        passed = false;
    }
    
    // Test Case 2: 3-Var Majority (F = Sum(3, 5, 6, 7))
    const tc2 = solveKMap([3, 5, 6, 7], [], 3);
    const tc2Str = formatSOP(tc2, 3);
    // Expect: AB + BC + AC in some permutation
    const tc2Terms = tc2Str.split(' + ');
    const tc2Valid = tc2Terms.length === 3 && 
                     tc2Terms.includes('AB') && 
                     tc2Terms.includes('BC') && 
                     tc2Terms.includes('AC');
    if (!tc2Valid) {
        console.error("Test Case 2 failed. Got:", tc2Str);
        passed = false;
    }
    
    // Test Case 3: 4-Var Corners wrapping (F = Sum(0, 2, 8, 10))
    const tc3 = solveKMap([0, 2, 8, 10], [], 4);
    const tc3Str = formatSOP(tc3, 4);
    // Expect: B'D'
    const tc3Valid = tc3Str === "B'D'";
    if (!tc3Valid) {
        console.error("Test Case 3 failed. Got:", tc3Str);
        passed = false;
    }
    
    // Test Case 4: 4-Var Don't Cares (F = Sum(1, 3, 7, 11, 15) + d(0, 2, 5))
    // Minterms: 1, 3, 7, 11, 15
    // Don't Cares: 0, 2, 5
    // Simplification should group columns CD = 11, and rows AB = 00 with CD.
    // CD = 11 covers: 3, 7, 11, 15 (which is correct, covers 4 minterms)
    // Leftover is cell 1. Can we group it with 0, 2, 3 (which are minterm/dont-cares) to form A'B'?
    // Cells 0, 1, 2, 3 covers: A'B'.
    // Covered minterms by CD and A'B' are:
    // CD: 3, 7, 11, 15
    // A'B': 0, 1, 2, 3 (covers minterms 1, 3)
    // All original minterms (1, 3, 7, 11, 15) are covered!
    // Result: CD + A'B'
    const tc4 = solveKMap([1, 3, 7, 11, 15], [0, 2, 5], 4);
    const tc4Str = formatSOP(tc4, 4);
    const tc4Valid = tc4Str === "CD + A'B'" || tc4Str === "A'B' + CD";
    if (!tc4Valid) {
        console.error("Test Case 4 failed. Got:", tc4Str);
        passed = false;
    }
    
    // Test Case 5: POS 3-Var Majority Maxterms (Grouping 0s: 0, 1, 2, 4)
    // 0s are 0, 1, 2, 4. No don't cares.
    // POS result should be (A + B)(B + C)(A + C)
    const tc5 = solveKMap([0, 1, 2, 4], [], 3, true);
    const tc5Str = formatPOS(tc5, 3);
    const tc5Terms = tc5Str.replace(/\(|\)/g, ' ').trim().split(/\s+/).filter(s => s !== '+');
    // Result: (A+B)(B+C)(A+C) in some order of terms and terms additions
    // Check if the output matches expected POS logic
    const tc5Valid = tc5Str.includes('A + B') && tc5Str.includes('B + C') && tc5Str.includes('A + C');
    if (!tc5Valid) {
        console.error("Test Case 5 failed. Got:", tc5Str);
        passed = false;
    }

    if (passed) {
        console.log("All Solver Diagnostics PASSED successfully!");
        showToast("Diagnostics Passed: Boolean Minimizer verified.", "success");
    } else {
        console.error("Diagnostics FAILED. Checking QM logic required.");
        showToast("Diagnostics Failed: Solver mismatch detected.", "error");
    }
}

// ----------------------------------------------------
// ON INITIAL LOAD
// ----------------------------------------------------
document.addEventListener('DOMContentLoaded', () => {
    // Run solvers diagnostics
    setTimeout(runDiagnostics, 500);
    
    // Initialize with 4 variables default
    updateApp();
});
