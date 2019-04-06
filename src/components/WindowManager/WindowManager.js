import React, { Component } from "react";
import { ProgramContext } from "../../contexts/programs";

class WindowManager extends Component {
  static contextType = ProgramContext;

  render() {
    return (
      <>
        {this.context.activePrograms
          .filter(prog => !prog.minimized)
          .map(prog => (
            <prog.Component
              {...prog}
              key={prog.id || prog.key}
              onClose={this.context.onClose}
              onMinimize={this.context.onMinimize}
              moveToTop={this.context.moveToTop}
              isActive={prog.id === this.context.activeId}
            />
          ))}
      </>
    );
  }
}

export default WindowManager;
