#!/usr/bin/env python3
import subprocess
import sys
import re

def get_commits(project_dir):
    """Get commits for a project directory."""
    cmd = [
        'git', 'log', 
        '--format=%as|%h|%s',
        '--shortstat',
        '--no-merges',
        '--', '.'
    ]
    
    try:
        result = subprocess.run(
            cmd,
            cwd=project_dir,
            capture_output=True,
            text=True,
            check=True
        )
        return result.stdout
    except subprocess.CalledProcessError:
        return None

def parse_commits(output):
    """Parse git log output into structured data."""
    if not output:
        return []
    
    commits = []
    lines = output.strip().split('\n')
    
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if not line:
            i += 1
            continue
            
        # Parse commit line
        parts = line.split('|', 2)
        if len(parts) != 3:
            i += 1
            continue
            
        date, hash_val, message = parts
        
        # Escape pipes in message
        message = message.replace('|', ' ')
        
        # Look ahead for stats line (might be next line or after a blank line)
        stats = '-'
        check_idx = i + 1
        
        # Skip blank lines
        while check_idx < len(lines) and not lines[check_idx].strip():
            check_idx += 1
        
        # Check if next non-blank line is a stat line
        if check_idx < len(lines):
            stat_line = lines[check_idx].strip()
            # Check if this is a stat line (contains "file" and "changed")
            if 'file' in stat_line and 'changed' in stat_line and '|' not in stat_line:
                # Parse insertions and deletions
                ins_match = re.search(r'(\d+) insertion', stat_line)
                del_match = re.search(r'(\d+) deletion', stat_line)
                
                ins = ins_match.group(1) if ins_match else '0'
                dels = del_match.group(1) if del_match else '0'
                
                if ins != '0' or dels != '0':
                    stats = f'+{ins}/-{dels}'
        
        commits.append({
            'date': date,
            'hash': hash_val,
            'message': message,
            'stats': stats
        })
        
        i += 1
    
    return commits

def format_org_table(project_name, commits):
    """Format commits as an org-mode table."""
    lines = [
        f"** {project_name}",
        "",
        "| Date | Hash | Message | +/- |",
        "|------+------+---------+-----|"
    ]
    
    if not commits:
        lines.append("| - | - | No commits found | - |")
    else:
        for c in commits:
            lines.append(f"| {c['date']} | ={c['hash']}= | {c['message']} | {c['stats']} |")
    
    lines.append("")
    return '\n'.join(lines)

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: format-commits.py PROJECT_DIR PROJECT_NAME")
        sys.exit(1)
    
    project_dir = sys.argv[1]
    project_name = sys.argv[2]
    
    output = get_commits(project_dir)
    commits = parse_commits(output)
    print(format_org_table(project_name, commits))
