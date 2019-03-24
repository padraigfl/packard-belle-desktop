import React, { Component } from "react";
import ExplorerWindow from "../ExplorerWindow";
import { ProgramContext } from "../../contexts/programs";

class TaskBar extends Component {
  static contextType = ProgramContext;

  render() {
    return (
      <>
        {this.context.activePrograms.map(prog => (
          <ExplorerWindow
            {...prog}
            key={prog.id || prog.key}
            onClose={this.context.onClose}
            moveToTop={this.context.moveToTop}
            isActive={prog.id === this.context.activeId}
          />
        ))}
      </>
    );
  }
}

export default TaskBar;
