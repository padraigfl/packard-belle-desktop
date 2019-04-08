import React from "react";
import cx from "classnames";
import Window from "../tools/Window";
import "./_StandardWindow.scss";

export const buildMenu = props => [
  {
    title: "File",
    options: [
      {
        title: "New",
        onClick:
          props.multiWindow && props.onOpen && (() => props.onOpen(props.id))
      },
      { title: "Open", isDisabled: true },
      { title: "Close", onClick: () => props.onClose(props.id) }
    ]
  },
  {
    title: "Help",
    options: [{ title: `About ${props.title}`, isDisabled: true }]
  }
];

const StandardWindow = props => (
  <Window
    {...props}
    initialHeight={props.initialHeight || 200}
    initialWidth={props.initialWidth || 200}
  >
    {rnd => (
      <props.Component
        title={props.title}
        icon={props.icon}
        footer={props.footer}
        onOpen={props.multiWindow && (() => props.onOpen(props.id))}
        onClose={() => props.onClose(props.id)}
        onMinimize={() => props.onMinimize(props.id)}
        onRestore={rnd.restore}
        onMaximize={rnd.maximize}
        changingState={rnd.state.isDragging || rnd.state.isResizing}
        maximizeOnOpen={rnd.context.isMobile}
        className={cx(props.className, { "Window--active": props.isActive })}
        menuOptions={props.menuOptions}
        hasMenu={props.hasMenu}
        explorerOptions={props.explorerOptions}
        data={props.data}
      >
        {props.children}
      </props.Component>
    )}
  </Window>
);
StandardWindow.defaultProps = {
  hasMenu: true
};

export default StandardWindow;
