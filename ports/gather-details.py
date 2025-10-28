#!/usr/bin/env python3
"""Extract Summary and Fil-C Compatibility Changes from all info/*.md files."""

import re
from pathlib import Path

def extract_sections(content, filename):
    """Extract Summary and Fil-C Compatibility Changes sections."""
    
    # Split by top-level headers (##) only
    sections = {}
    current_section = None
    current_content = []
    
    for line in content.split('\n'):
        # Check if this is a top-level header (## but not ###)
        header_match = re.match(r'^##\s+(.+)$', line)
        if header_match:
            # Save previous section
            if current_section:
                sections[current_section.lower()] = '\n'.join(current_content).strip()
            # Start new section
            current_section = header_match.group(1).strip()
            current_content = []
        elif current_section:
            # Add line to current section (including ### subsections)
            current_content.append(line)
    
    # Save last section
    if current_section:
        sections[current_section.lower()] = '\n'.join(current_content).strip()
    
    # Extract what we need
    result = {}
    
    # Look for summary (case insensitive)
    for key in sections:
        if 'summary' in key:
            result['summary'] = sections[key]
            break
    
    # Look for Fil-C Compatibility Changes (case insensitive)
    for key in sections:
        if 'fil-c' in key and 'compatib' in key:
            result['changes'] = sections[key]
            break
    
    # Alert if missing
    if 'summary' not in result:
        print(f"  ⚠️  No Summary section found in {filename}")
    if 'changes' not in result:
        print(f"  ⚠️  No Fil-C Compatibility Changes section found in {filename}")
    
    return result

def main():
    info_dir = Path('info')
    output_file = Path('info/all-details.md')
    
    # Get all .md files except special ones
    md_files = sorted([f for f in info_dir.glob('*.md') 
                      if f.name not in ['README.md', 'SUMMARY.md', 'all-details.md', 'commits.org']])
    
    print(f"Processing {len(md_files)} files...")
    
    with output_file.open('w') as out:
        out.write("# Fil-C Port Details\n\n")
        out.write("Detailed summaries and compatibility changes for all ported projects.\n\n")
        
        for md_file in md_files:
            # Extract project name from filename
            project_name = md_file.stem
            
            print(f"Processing {project_name}...")
            
            # Read file
            content = md_file.read_text()
            
            # Extract first line as title (should be "# Project Version")
            first_line = content.split('\n')[0]
            if first_line.startswith('#'):
                title = first_line.lstrip('#').strip()
            else:
                title = project_name
            
            # Extract sections
            sections = extract_sections(content, md_file.name)
            
            # Write to output
            out.write(f"## {title}\n\n")
            
            if 'summary' in sections:
                out.write(f"{sections['summary']}\n\n")
            
            if 'changes' in sections:
                out.write(f"### Fil-C Compatibility Changes\n\n")
                out.write(f"{sections['changes']}\n\n")
            
            out.write("---\n\n")
    
    print(f"\n✓ Wrote {output_file}")

if __name__ == '__main__':
    main()
