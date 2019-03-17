import React, { Component } from "react";
import { TaskBar as TaskBarComponent } from "packard-belle";
import { ProgramContext } from "../../contexts/programs";

class TaskBar extends Component {
  static contextType = ProgramContext;

  render() {
    return (
      <ProgramContext.Consumer>
        {context => (
          <TaskBarComponent
            options={context.startMenu}
            openWindows={context.openWindows}
          />
        )}
      </ProgramContext.Consumer>
    );
  }
}

export default TaskBar;
